open Core

type criterion = Bap_emu_slice.location = Reg of string | Mem of int64 * int
[@@deriving compare, equal, sexp]

type event =
  | Instruction of { pc : int64; thread : int }
  | Block of { pc : int64; size : int; thread : int }
  | Branch of { site : int64; target : int64; taken : bool; thread : int }
  | Call of { site : int64; targets : (int64 * int) list; thread : int }
  | Syscall of { number : int64; args : int64 list; thread : int }
  | Capture of { site : int64; values : int64 list; thread : int }
  | Write of {
      pc : int64;
      addr : int64;
      size : int;
      value : int64;
      thread : int;
    }
[@@deriving compare, equal, sexp]

type kind =
  | Instruction_kind
  | Block_kind
  | Branch_kind
  | Call_kind
  | Syscall_kind
  | Capture_kind
  | Write_kind
[@@deriving compare, equal, sexp]

type address_field = Pc | Site | Target [@@deriving compare, equal, sexp]

type values_field = Arguments | Registers | Targets
[@@deriving compare, equal, sexp]

type side = Left | Right [@@deriving compare, equal, sexp]

type reason =
  | Kind_mismatch of { left : kind; right : kind }
  | Thread_mismatch of { left : int; right : int }
  | Address_mismatch of { field : address_field; left : int64; right : int64 }
  | Size_mismatch of { left : int; right : int }
  | Taken_mismatch of { left : bool; right : bool }
  | Number_mismatch of { left : int64; right : int64 }
  | Values_mismatch of {
      field : values_field;
      position : int;
      left : int64;
      right : int64;
    }
  | Values_length_mismatch of { field : values_field; left : int; right : int }
  | Call_count_mismatch of { target : int64; left : int; right : int }
  | Memory_address_mismatch of {
      left : int64;
      right : int64;
      size : int;
      criterion : criterion;
    }
  | Memory_size_mismatch of {
      left : int;
      right : int;
      addr : int64;
      criterion : criterion;
    }
  | Memory_value_mismatch of {
      left : int64;
      right : int64;
      addr : int64;
      size : int;
      criterion : criterion;
    }
  | Missing of { side : side; expected : kind }
[@@deriving compare, equal, sexp]

type normalize = { address : int64 -> int64; value : int64 -> int64 }

let normalization ?(address = Fn.id) ?(value = Fn.id) () = { address; value }
let identity = normalization ()

type difference = {
  index : int;
  reason : reason;
  before : event list;
  left : event list;
  right : event list;
}
[@@deriving compare, equal, sexp]

type result = Equal | Difference of difference
[@@deriving compare, equal, sexp]

let kind = function
  | Instruction _ -> Instruction_kind
  | Block _ -> Block_kind
  | Branch _ -> Branch_kind
  | Call _ -> Call_kind
  | Syscall _ -> Syscall_kind
  | Capture _ -> Capture_kind
  | Write _ -> Write_kind

let thread = function
  | Instruction { thread; _ }
  | Block { thread; _ }
  | Branch { thread; _ }
  | Call { thread; _ }
  | Syscall { thread; _ }
  | Capture { thread; _ }
  | Write { thread; _ } ->
      thread

let normalize_event n = function
  | Instruction { pc; thread } -> Instruction { pc = n.address pc; thread }
  | Block { pc; size; thread } -> Block { pc = n.address pc; size; thread }
  | Branch { site; target; taken; thread } ->
      Branch { site = n.address site; target = n.address target; taken; thread }
  | Call { site; targets; thread } ->
      Call
        {
          site = n.address site;
          targets =
            List.map targets ~f:(fun (target, count) ->
                (n.address target, count));
          thread;
        }
  | Syscall { number; args; thread } ->
      Syscall { number; args = List.map args ~f:n.value; thread }
  | Capture { site; values; thread } ->
      Capture
        { site = n.address site; values = List.map values ~f:n.value; thread }
  | Write { pc; addr; size; value; thread } ->
      Write
        {
          pc = n.address pc;
          addr = n.address addr;
          size;
          value = n.value value;
          thread;
        }

let first checks = List.find_map checks ~f:(fun check -> check ())

let address field left right =
  if Int64.equal left right then None
  else Some (Address_mismatch { field; left; right })

let size left right =
  if left = right then None else Some (Size_mismatch { left; right })

let values field left right =
  let rec loop position left right =
    match (left, right) with
    | x :: xs, y :: ys when Int64.equal x y -> loop (position + 1) xs ys
    | x :: _, y :: _ ->
        Some (Values_mismatch { field; position; left = x; right = y })
    | [], [] -> None
    | _ ->
        Some
          (Values_length_mismatch
             { field; left = List.length left; right = List.length right })
  in
  loop 0 left right

let compare_targets left right =
  let rec loop left right =
    match (left, right) with
    | (a, n) :: xs, (b, m) :: ys -> (
        match address Target a b with
        | Some _ as different -> different
        | None ->
            if n <> m then
              Some (Call_count_mismatch { target = a; left = n; right = m })
            else loop xs ys)
    | [], [] -> None
    | _ ->
        Some
          (Values_length_mismatch
             {
               field = Targets;
               left = List.length left;
               right = List.length right;
             })
  in
  loop left right

let reason ~normalize original_left original_right =
  let left = normalize_event normalize original_left
  and right = normalize_event normalize original_right in
  if not (equal_kind (kind left) (kind right)) then
    Some (Kind_mismatch { left = kind left; right = kind right })
  else if thread left <> thread right then
    Some (Thread_mismatch { left = thread left; right = thread right })
  else
    match (left, right) with
    | Instruction a, Instruction b -> address Pc a.pc b.pc
    | Block a, Block b ->
        first
          [ (fun () -> address Pc a.pc b.pc); (fun () -> size a.size b.size) ]
    | Branch a, Branch b ->
        first
          [
            (fun () -> address Site a.site b.site);
            (fun () -> address Target a.target b.target);
            (fun () ->
              if Bool.equal a.taken b.taken then None
              else Some (Taken_mismatch { left = a.taken; right = b.taken }));
          ]
    | Call a, Call b ->
        first
          [
            (fun () -> address Site a.site b.site);
            (fun () -> compare_targets a.targets b.targets);
          ]
    | Syscall a, Syscall b ->
        first
          [
            (fun () ->
              if Int64.equal a.number b.number then None
              else Some (Number_mismatch { left = a.number; right = b.number }));
            (fun () -> values Arguments a.args b.args);
          ]
    | Capture a, Capture b ->
        first
          [
            (fun () -> address Site a.site b.site);
            (fun () -> values Registers a.values b.values);
          ]
    | Write a, Write b -> (
        match original_left with
        | Write original ->
            let criterion = Mem (original.addr, original.size) in
            first
              [
                (fun () -> address Pc a.pc b.pc);
                (fun () ->
                  if Int64.equal a.addr b.addr then None
                  else
                    Some
                      (Memory_address_mismatch
                         {
                           left = a.addr;
                           right = b.addr;
                           size = original.size;
                           criterion;
                         }));
                (fun () ->
                  if a.size = b.size then None
                  else
                    Some
                      (Memory_size_mismatch
                         {
                           left = a.size;
                           right = b.size;
                           addr = original.addr;
                           criterion;
                         }));
                (fun () ->
                  if Int64.equal a.value b.value then None
                  else
                    Some
                      (Memory_value_mismatch
                         {
                           left = a.value;
                           right = b.value;
                           addr = original.addr;
                           size = original.size;
                           criterion;
                         }));
              ]
        | _ -> assert false)
    | _ -> assert false

let compare ?(context = 3) ?(normalize = identity) left right =
  if context < 0 then invalid_arg "Bap_emu.Compare.compare: negative context";
  let difference index before left right reason =
    Difference
      {
        index;
        reason;
        before = List.rev before;
        left = List.take left context;
        right = List.take right context;
      }
  in
  let rec loop index before left right =
    match (left, right) with
    | [], [] -> Equal
    | [], r :: _ ->
        difference index before left right
          (Missing { side = Left; expected = kind r })
    | l :: _, [] ->
        difference index before left right
          (Missing { side = Right; expected = kind l })
    | l :: ls, r :: rs -> (
        match reason ~normalize l r with
        | Some why -> difference index before left right why
        | None ->
            let before =
              if context = 0 then [] else List.take (l :: before) context
            in
            loop (index + 1) before ls rs)
  in
  loop 0 [] left right

let syscall ~thread number args = Syscall { number; args; thread }
