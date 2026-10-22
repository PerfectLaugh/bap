open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Bap_c.Std

let registers =
  Primus.Machine.State.declare ~uuid:"3dd2b905-c019-4466-800f-95b13d7da85e"
    ~name:"backend-registers"
  @@ fun proj ->
  Project.disasm proj |> Disasm.insns
  |> Seq.fold ~init:Int.Map.empty ~f:(fun regs (_, insn) ->
      Insn.ops insn
      |> Array.fold ~init:regs ~f:(fun regs -> function
        | Op.Reg r -> Map.set regs ~key:(Reg.code r) ~data:(Reg.name r)
        | _ -> regs))

module Closure (Machine : Primus.Machine.S) = struct
  module Lisp = Primus.Lisp.Make (Machine)
  module Value = Primus.Value.Make (Machine)
  module Eval = Primus.Interpreter.Make (Machine)
  module Closure = Primus.Lisp.Closure.Make (Machine)
  module Linker = Primus.Linker.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)

  type value = Value.t
  type 'a m = 'a Machine.t

  open Machine.Syntax
  open Machine.Let

  let failf = Lisp.failf
  let addr_width = Machine.gets Project.target >>| Theory.Target.bits
  let endian = Machine.arch >>| Arch.endian
  let null = addr_width >>= Value.zero
  let negone = null >>= Value.lnot
  let false_ = Value.zero 1
  let true_ = Value.one 1

  let reduce null op = function
    | [] -> null
    | x :: xs -> Machine.List.fold xs ~init:x ~f:op

  let msb x =
    let hi = Value.bitwidth x - 1 in
    Value.extract ~hi ~lo:hi x

  let to_int e =
    match Word.to_int (Value.to_word e) with
    | Ok x -> Machine.return x
    | Error _ -> failf "expected smallint" ()

  let rec all f = function
    | [] -> true_
    | x :: xs ->
        f x >>= fun x ->
        if Value.is_one x then all f xs >>= fun xs -> Eval.binop AND x xs
        else Machine.return x

  let ordered order xs =
    let rec ordered = function
      | [] | [ _ ] -> true_
      | x :: (y :: _ as rest) ->
          order x y >>= fun r ->
          if Value.is_one r then ordered rest >>= fun r' -> Eval.binop AND r r'
          else Machine.return r
    in
    ordered xs

  let reg_name code =
    Machine.Local.get registers >>= fun regs ->
    let code = Word.to_int_exn @@ Primus.Value.to_word code in
    match Map.find regs code with
    | None -> failf "unresolved intruction register %#x" code ()
    | Some name -> Value.Symbol.to_value name

  let exec_addr addr =
    Linker.exec (`addr (Primus.Value.to_word addr)) >>= fun () ->
    Eval.halt >>= never_returns

  let exec_symbol name =
    Value.Symbol.of_value name >>= fun name ->
    Linker.exec (`symbol name) >>= fun () -> Eval.halt >>= never_returns

  let is_zero =
    all @@ fun x ->
    Value.zero (Value.bitwidth x) >>= fun z -> Eval.binop EQ x z

  let is_positive = all @@ fun x -> msb x >>= Eval.unop NOT

  let word_width args =
    addr_width >>= fun width ->
    List.map args ~f:Value.bitwidth |> List.max_elt ~compare:Int.compare
    |> function
    | None -> Value.of_int ~width width
    | Some x -> Value.of_int ~width x

  let exit_with code =
    Eval.exit code >>| Nothing.unreachable_code >>= fun () -> Value.b0

  (* the byte in hex, or ?? if it is not mapped, or -- if it is not
     readable, as its load would be a page fault *)
  let dump_byte addr =
    Memory.protection addr >>= function
    | None -> Machine.return ("??", '.')
    | Some { readable = false; _ } -> Machine.return ("--", '.')
    | Some _ ->
        Memory.load addr >>| fun x ->
        let c = Word.to_int_exn x in
        let c = Char.of_int_exn c in
        (sprintf "%02x" (Char.to_int c), if Char.is_print c then c else '.')

  (* sends the lines of 16 bytes, like hexdump -C *)
  let dump_memory_region addr len =
    let* len = to_int len in
    let addr = Value.to_word addr in
    let rec lines off =
      if off >= len then Machine.return ()
      else
        let base = Word.(addr ++ off) in
        let n = Int.min 16 (len - off) in
        let* bytes =
          Machine.List.map (List.init n ~f:Fn.id) ~f:(fun i ->
              dump_byte Word.(base ++ i))
        in
        let hex = List.map bytes ~f:fst |> String.concat ~sep:" " in
        let text = List.map bytes ~f:snd |> String.of_char_list in
        let* () = Lisp.say "%a: %-47s |%s|" Addr.pps base hex text in
        lines (off + 16)
    in
    let* () = lines 0 in
    Value.b0

  (* the outputs, e.g., of the observations, are flushed, as [exit]
     flushes all channels *)
  let bap_exit code =
    let* code = to_int code in
    let* () = Lisp.say "bap exits with %d" code in
    Stdlib.exit code

  let negone = Value.one 8
  let zero = Value.zero 8
  let value_to_int x = Value.to_word x |> Word.to_int

  let make_static_generator width x =
    match Word.to_int x with
    | Ok x -> Ok (Some (Primus.Generator.static ~width x))
    | _ -> Or_error.errorf "memory-allocate: fill in value must fit into int"

  let is_nil x = Word.equal Word.b0 (Value.to_word x)

  let make_uniform_generator ~width ~min ~max =
    let nomin = is_nil min and nomax = is_nil max in
    if nomin && nomax then Ok None
    else
      match (value_to_int min, value_to_int max) with
      | Ok min, Ok max ->
          let min = if nomin then None else Some min
          and max = if nomax then None else Some max in
          let g = Primus.Generator.Random.Seeded.lcg ~width ?min ?max () in
          Ok (Some g)
      | _ ->
          Or_error.errorf "memory-allocate: random values do not fit into int"

  let memory_allocate addr size rest =
    let module Memory = Primus.Memory.Make (Machine) in
    Machine.gets Project.target >>| Theory.Target.bits >>= fun width ->
    let gen =
      match rest with
      | [] -> Ok None
      | [ x ] -> make_static_generator width (Value.to_word x)
      | [ min; max ] -> make_uniform_generator ~width ~min ~max
      | _ -> Or_error.errorf "bad generator"
    in
    if Result.is_error gen then
      failf "memory-allocate: bad generator specification" ()
    else
      let generator = Or_error.ok_exn gen in
      let lower = Value.to_word addr in
      let upper = Word.(lower + pred (Value.to_word size)) in
      Memory.add_region ?generator ~lower ~upper () >>= fun () -> zero

  (* the protection is the PROT_READ, PROT_WRITE, and PROT_EXEC bits of
     POSIX, 1, 2, and 4 *)
  let memory_protect addr len prot =
    let module Memory = Primus.Memory.Make (Machine) in
    let len = Value.to_word len and prot = Value.to_word prot in
    if Word.is_zero len then zero
    else
      let has bit =
        not Word.(is_zero (prot land of_int ~width:(bitwidth prot) bit))
      in
      let lower = Value.to_word addr in
      let upper = Word.(lower + pred len) in
      Memory.protect ~lower ~upper
        { readable = has 1; writable = has 2; executable = has 4 }
      >>= fun () -> zero

  let memory_read addr = Eval.load addr BigEndian `r8
  let memory_write a x = Eval.store a x BigEndian `r8 >>= fun () -> Value.succ a

  let extract hi lo x =
    to_int hi >>= fun hi ->
    to_int lo >>= fun lo -> Eval.extract ~hi ~lo x

  let symbol_concat syms =
    Machine.List.map syms ~f:Value.Symbol.of_value >>= fun strs ->
    Value.Symbol.to_value (String.concat strs)

  let set_value reg x =
    Value.Symbol.of_value reg >>= fun reg ->
    let typ = Type.imm (Word.bitwidth (Value.to_word x)) in
    let var = Var.create reg typ in
    Eval.set var x >>| fun () -> x

  let symbol_of_cstring ptr =
    let module Mem = Primus.Memory.Make (Machine) in
    let rec build chars ptr =
      Mem.load ptr >>= fun x ->
      if Word.is_zero x then
        Machine.return @@ String.of_char_list (List.rev chars)
      else
        let char = Word.to_int_exn x |> Char.of_int_exn in
        build (char :: chars) (Word.succ ptr)
    in
    build [] (Value.to_word ptr) >>= Value.Symbol.to_value

  type dir = [ `down | `up ] [@@deriving equal]

  let stack_slot exp =
    let open Bil.Types in
    match exp with
    | BinOp (PLUS, Var sp, Int off) -> Some (sp, `down, off)
    | BinOp (MINUS, Var sp, Int off) -> Some (sp, `up, off)
    | _ -> None

  let update_frame slot addr n =
    match (slot, stack_slot addr) with
    | slot, None -> slot
    | None, Some (sp, dir, off) -> Some (sp, dir, Word.(off ++ Size.in_bytes n))
    | Some (sp, dir, off), Some (sp', dir', off') ->
        if Var.same sp sp' && equal_dir dir dir' then
          let off = Word.max off off' in
          Some (sp, dir, Word.(off ++ Size.in_bytes n))
        else Some (sp, dir, off)

  let find_max_slot =
    Seq.fold ~init:None ~f:(fun slot arg ->
        match Arg.rhs arg with
        | Bil.Load (_, addr, _, n) -> update_frame slot addr n
        | _ -> slot)

  let allocate_stack_frame args =
    match find_max_slot args with
    | None -> Machine.return None
    | Some (sp, dir, max) ->
        let sign = if equal_dir dir `down then Bil.MINUS else Bil.PLUS in
        Eval.get sp >>= fun sp_value ->
        Eval.const max >>= fun frame_size ->
        Eval.binop sign sp_value frame_size >>= Eval.set sp >>= fun () ->
        Machine.return (Some (sp, sp_value))

  (* The return address of the subroutine of a target, whose calls push
     it on the stack, e.g., x86, is at the stack pointer, below the
     arguments, which the frame reserves, so the subroutine returns to
     the address, to which the current one returns, e.g., the stub of
     Lisp, which the executors of the machine treat as its return, and
     the stack stays balanced, when the subroutines are invoked again,
     e.g., by _initterm of msvcrt. *)
  let push_return_address frame =
    Machine.gets Project.target >>= fun target ->
    match
      ( Theory.Target.reg target Theory.Role.Register.link,
        Theory.Target.reg target Theory.Role.Register.stack_pointer )
    with
    | None, Some sp -> (
        let sp = Var.reify sp in
        let width = Theory.Target.code_addr_size target in
        let size = Size.of_int_exn width in
        let endian =
          if Theory.Endianness.(Theory.Target.endianness target = eb) then
            BigEndian
          else LittleEndian
        in
        Eval.get sp >>= fun top ->
        (match frame with
          | Some (_, caller) -> Eval.load caller endian size
          | None -> Eval.load top endian size)
        >>= fun ret ->
        match frame with
        | Some _ -> Eval.store top ret endian size >>| fun () -> frame
        | None ->
            Eval.const (Word.of_int ~width (width / 8)) >>= fun n ->
            Eval.binop Bil.MINUS top n >>= fun slot ->
            Eval.set sp slot >>= fun () ->
            Eval.store slot ret endian size >>| fun () -> Some (sp, top))
    | _ -> Machine.return frame

  let is_out_intent a = match Arg.intent a with Some Out -> true | _ -> false

  let eval_sub : value list -> 'x = function
    | [] -> failf "invoke-subroutine: requires at least one argument" ()
    | sub_addr :: sub_args -> (
        Machine.get () >>= fun proj ->
        let find addr =
          Term.enum sub_t (Project.program proj)
          |> Seq.find ~f:(fun sub ->
              match Term.get_attr sub address with
              | None -> false
              | Some x -> Word.(x = addr))
        in
        let addr = Value.to_word sub_addr in
        (* the pointers to the Thumb code of ARM have the lower bit set *)
        let found =
          match find addr with
          | None when Word.(is_one (extract_exn ~hi:0 ~lo:0 addr)) ->
              find Word.(addr - one (bitwidth addr))
          | found -> found
        in
        (* the function, that the program has no subroutine for, e.g.,
           the stripped one, takes the words, as the C ABI passes them *)
        let anonymous () =
          let target = Project.target proj in
          match C.Abi.lookup target with
          | None -> None
          | Some abi ->
              let word = C.Type.basic `slong in
              let proto : C.Type.proto =
                {
                  return = word;
                  args =
                    List.mapi sub_args ~f:(fun i _ -> (sprintf "x%d" i, word));
                  variadic = false;
                }
              in
              let sub = Term.set_attr (Sub.create ()) address addr in
              Some (C.Abi.apply abi (C.Abi.model target) [] proto sub)
        in
        match Option.first_some found (anonymous ()) with
        | None ->
            failf "invoke-subroutine: no function for %a" Value.pps sub_addr ()
        | Some sub -> (
            let args = Term.enum arg_t sub in
            allocate_stack_frame args >>= push_return_address >>= fun frame ->
            Seq.zip args (Seq.of_list sub_args)
            |> Machine.Seq.iter ~f:(fun (arg, x) ->
                let open Bil.Types in
                if not (is_out_intent arg) then Eval.assign (Arg.rhs arg) x
                else Machine.return ())
            >>= fun () ->
            Linker.exec (`addr (Option.value_exn (Term.get_attr sub address)))
            >>= fun () ->
            (* the result is where the function returns it, e.g., RAX,
               as the variable of the argument is assigned only by the
               interpreter, not by the code, that runs elsewhere, e.g.,
               in Unicorn, or of the anonymous function *)
            Machine.Seq.find_map args ~f:(fun arg ->
                if is_out_intent arg then Eval.exp (Arg.rhs arg) >>| Option.some
                else Machine.return None)
            >>= fun rval ->
            let teardown_frame =
              match frame with
              | Some (sp, bp) -> Eval.set sp bp
              | None -> Machine.return ()
            in
            teardown_frame >>= fun () ->
            match rval with
            | None -> Eval.const Word.b0
            | Some rval -> Machine.return rval))

  let run args =
    Closure.name >>= fun name ->
    match (name, args) with
    | "reg-name", [ arg ] -> reg_name arg
    | "exec-addr", [ addr ] -> exec_addr addr
    | "exec-symbol", [ dst ] -> exec_symbol dst
    | "is-zero", args -> is_zero args
    | "is-positive", args -> is_positive args
    | "is-negative", args -> all msb args
    | "word-width", args -> word_width args
    | "exit-with", [ arg ] -> exit_with arg
    | "bap-exit", [ arg ] -> bap_exit arg
    | "dump-memory-region", [ addr; len ] -> dump_memory_region addr len
    | "memory-allocate", x :: y :: rest -> memory_allocate x y rest
    | "memory-protect", [ a; n; p ] -> memory_protect a n p
    | "memory-read", [ x ] -> memory_read x
    | "memory-write", [ a; x ] -> memory_write a x
    | "get-current-program-counter", [] -> Eval.pc >>= Value.of_word
    | "+", args -> reduce null (Eval.binop Bil.PLUS) args
    | "-", args -> reduce null (Eval.binop Bil.MINUS) args
    | "/", args -> reduce null (Eval.binop Bil.DIVIDE) args
    | "s/", args -> reduce null (Eval.binop Bil.SDIVIDE) args
    | "*", args -> reduce null (Eval.binop Bil.TIMES) args
    | "mod", args -> reduce null (Eval.binop Bil.MOD) args
    | "signed-mod", args -> reduce null (Eval.binop Bil.SMOD) args
    | "lshift", [ x; y ] -> Eval.binop Bil.lshift x y
    | "rshift", [ x; y ] -> Eval.binop Bil.rshift x y
    | "arshift", [ x; y ] -> Eval.binop Bil.arshift x y
    | "=", args -> ordered (Eval.binop EQ) args
    | "/=", args -> ordered (Eval.binop NEQ) args
    | "logand", args -> reduce negone (Eval.binop Bil.AND) args
    | "logor", args -> reduce negone (Eval.binop Bil.OR) args
    | "logxor", args -> reduce negone (Eval.binop Bil.XOR) args
    | "concat", args -> reduce false_ Eval.concat args
    | "extract", [ hi; lo; x ] -> extract hi lo x
    | "not", [ x ] -> is_zero [ x ]
    | "lnot", [ x ] -> Eval.unop Bil.NOT x
    | "neg", [ x ] -> Eval.unop Bil.NEG x
    | "<", args -> ordered (Eval.binop LT) args
    | ">", args -> ordered (fun x y -> Eval.binop LT y x) args
    | "<=", args -> ordered (Eval.binop LE) args
    | ">=", args -> ordered (fun x y -> Eval.binop LE y x) args
    | "symbol-concat", args -> symbol_concat args
    | "set-symbol-value", [ reg; x ] -> set_value reg x
    | "symbol-of-string", [ ptr ] -> symbol_of_cstring ptr
    | "invoke-subroutine", args -> eval_sub args
    | name, _ -> Lisp.failf "%s: invalid number of arguments" name ()
end

module Primitives (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Lisp = Primus.Lisp.Make (Machine)
  module Eval = Primus.Interpreter.Make (Machine)

  let init () =
    let open Primus.Lisp.Type.Spec in
    let def name types docs = Lisp.define ~types ~docs name (module Closure) in
    Machine.sequence
      [
        def "exec-addr"
          (one int @-> any)
          "(exec-addr D) passes the control flow to D and never returns";
        def "exec-symbol"
          (one sym @-> any)
          "(exec-symbol D) passes the control flow to D and never returns";
        def "is-zero"
          (all any @-> bool)
          "(is-zero X Y ...) returns true if all arguments are zeros";
        def "is-positive"
          (all any @-> bool)
          "(is-positive X Y ...) returns true if all arguments are positive";
        def "is-negative"
          (all any @-> bool)
          "(is-negative X Y ...) returns true if all arguments are negative";
        def "word-width"
          (all int @-> int)
          "(word-width) returns machine word width in bits";
        def "exit-with"
          (one int @-> any)
          "(exit-with N) terminates program with the exit codeN";
        def "bap-exit"
          (one int @-> any)
          "(bap-exit N) exits bap with the exit code N at once, after it sends \
           the message, so the other machines and the next passes don't run, \
           and the outputs, e.g., of the observations, are flushed";
        def "dump-memory-region"
          (tuple [ int; int ] @-> any)
          "(dump-memory-region P N) sends the messages with the bytes of the \
           memory [P,P+N), 16 in a line, like hexdump -C, where ?? is a byte \
           that is not mapped, and -- a byte that is not readable. The bytes \
           of the allocated memory, which were never written, are generated, \
           as a load does";
        def "memory-protect"
          (tuple [ int; int; int ] @-> byte)
          "(memory-protect P N A) sets the access to the memory [P,P+N) to A, \
           the bits PROT_READ (1), PROT_WRITE (2), and PROT_EXEC (4) of POSIX, \
           so that a load from the memory that is not readable, or a store to \
           the memory that is not writable is a segmentation fault";
        def "memory-read"
          (one int @-> byte)
          "(memory-read A) loads one byte from the address A";
        def "memory-write"
          (tuple [ int; byte ] @-> int)
          "(memory-write A X) stores by X to A";
        def "memory-allocate"
          ((tuple [ int; int ] // all byte) @-> byte)
          "(memory-allocate P N V?) maps memory region [P,P+N), if V is\n\
          \         provided, then fills the newly mapped region with the \
           value V";
        def "get-current-program-counter" (unit @-> int)
          "(get-current-program-counter) returns current program cunnter";
        def "+"
          (all a @-> a)
          "(+ X Y ...) returns the sum of arguments, or 0 if there are\n\
          \         no arguments,";
        def "-"
          (all a @-> a)
          "(- X Y Z ...) returns X - Y - Z - ..., or 0 if there are no\n\
          \         arguments.";
        def "*"
          (all a @-> a)
          "(* X Y Z ...) returns the product of arguments or 0 if the list\n\
          \        of arguments is empty";
        def "/"
          (all a @-> a)
          "(/ X Y Z ...) returns X / Y / Z / ... or 0 if the list of\n\
          \         arguments is empty";
        def "s/"
          (all a @-> a)
          "(s/ X Y Z ...) returns X s/ Y s/ Z s/ ... or 0 if the list of\n\
          \         arguments is empty, where s/ is the signed division \
           operation";
        def "mod"
          (all a @-> a)
          "(mod X Y Z ...) returns X % Y % Z % ... or 0 if the list of\n\
          \         arguments is empty, where % is the modulo operation";
        def "signed-mod"
          (all a @-> a)
          "(signed-mod X Y Z ...) returns X % Y % Z % ... or 0 if the list of\n\
          \         arguments is empty, where % is the signed modulo operation";
        def "lshift"
          (tuple [ a; b ] @-> a)
          "(lshift X N) logically shifts X left by N bits";
        def "rshift"
          (tuple [ a; b ] @-> a)
          "(rshift X N) logically shifts X right by N bits";
        def "arshift"
          (tuple [ a; b ] @-> a)
          "(arshift X N) arithmetically shifts X right by N bits";
        def "="
          (all a @-> bool)
          "(= X Y Z ...) returns true if all arguments are equal. True\n\
          \        if the list of arguments is empty";
        def "/="
          (all a @-> bool)
          "(/= X Y Z ...) returns true if at least one argument is not\n\
          \         equal to another argument. Returns false if the list of\n\
          \         arguments is empty";
        def "logand"
          (all a @-> a)
          "(logand X Y Z ...) returns X & Y & Z & ... or 0 if the list of\n\
          \         arguments is empty, where & is the bitwise AND\n\
          \         operation. Returns ~0 if the list of arguments is empty";
        def "logor"
          (all a @-> a)
          "(logor X Y Z ...) returns X | Y | Z | ... or 0 if the list of\n\
          \         arguments is empty, where | is the bitwise OR operation";
        def "logxor"
          (all a @-> a)
          "(logxor X Y Z ...) returns X ^ Y ^ Z ^ ... or 0 if the list of\n\
          \         arguments is empty, where ^ is the bitwise XOR operation";
        def "concat"
          (all any @-> any)
          "(concat X Y Z ...) concatenates words X, Y, Z, ... into one\n\
          \         big word";
        def "extract"
          (tuple [ any; any; any ] @-> any)
          "(extract HI LO X) extracts bits from HI to LO (including\n\
          \           both) from the word X ";
        def "lnot" (one a @-> a) "(lnot X) returns the one complement of X";
        def "not" (one a @-> a) "(not X) returns true if X is zero";
        def "neg" (one a @-> a) "(neg X) returns the two complement of X";
        def "<"
          (all a @-> bool)
          "(< X Y Z ...) is true if the list of arguments is an\n\
          \         strict ascending chain or if it is empty";
        def ">"
          (all a @-> bool)
          "(< X Y Z ...) is true if the list of arguments is a\n\
          \         strict descending chain or if it is empty";
        def "<="
          (all a @-> bool)
          "(< X Y Z ...) is true if the list of arguments is an\n\
          \         ascending chain or if it is empty";
        def ">="
          (all a @-> bool)
          "(< X Y Z ...) is true if the list of arguments is a\n\
          \         descending chain or if it is empty";
        def "symbol-concat"
          (all sym @-> sym)
          "(symbol-concat X Y Z ...) returns a new symbol that is a\n\
          \        concatenation of symbols X,Y,Z,... ";
        def "set-symbol-value"
          (tuple [ sym; a ] @-> a)
          "(set-symbol-value S X) sets the value of the symbol S to X.\n\
          \         Returns X";
        def "reg-name"
          (one int @-> sym)
          "(reg-name N) returns the name of the register with the index N";
        def "symbol-of-string"
          (one int @-> sym)
          "(symbol-of-string ptr) returns a symbol from a\n\
          \         null-terminated string.";
        def "invoke-subroutine"
          ((one int // all any) @-> any)
          "(invoke-subroutine addr args ...) calls the subroutine\n\
          \         at the specified address.";
      ]
end

let init () =
  Primus.System.Repository.update ~package:"bap" "legacy-main" ~f:(fun s ->
      Primus.System.add_component s ~package:"bap" "lisp-primitives");
  Primus.Components.register_generic "lisp-primitives"
    (module Primitives)
    ~package:"bap" ~desc:"Provides the core set of Primus Lisp primitives.";
  Primus_lisp_ieee754.init ()
