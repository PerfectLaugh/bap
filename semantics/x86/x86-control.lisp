(declare (context (target x86)))
(require x86-common)

(in-package x86-common)

;;; BRANCHES, CALLS AND RETURNS
;;
;; The displacements are relative to the next instruction, the return
;; addresses are pushed and popped in the size of the operation.

(defun relative (off) (+ (get-next-program-counter) off))

(defun JMP_1 (off) (exec-addr (relative off)))
(defun JMP_2 (off) (exec-addr (relative off)))
(defun JMP_4 (off) (exec-addr (relative off)))
(defun JCC_1 (off cc) (when (condition cc) (exec-addr (relative off))))
(defun JCC_2 (off cc) (when (condition cc) (exec-addr (relative off))))
(defun JCC_4 (off cc) (when (condition cc) (exec-addr (relative off))))

(defun JMP16r (x) (exec-addr (cast-unsigned (word-width) x)))
(defun JMP16m (base scale index off seg) (exec-addr (cast-unsigned (word-width) (load-n 16 (ea base scale index off seg)))))
(defun JMP32r (x) (exec-addr (cast-unsigned (word-width) x)))
(defun JMP32m (base scale index off seg) (exec-addr (cast-unsigned (word-width) (load-n 32 (ea base scale index off seg)))))
(defun JMP64r (x) (exec-addr (cast-unsigned (word-width) x)))
(defun JMP64m (base scale index off seg) (exec-addr (cast-unsigned (word-width) (load-n 64 (ea base scale index off seg)))))

(defun call (n dst)
  (let ((d dst))
    (push-n n (get-next-program-counter))
    (exec-addr d)))

(defun CALLpcrel16 (off) (call 16 (relative off)))
(defun CALLpcrel32 (off) (call 32 (relative off)))
(defun CALL64pcrel32 (off) (call 64 (relative off)))
(defun CALL16r (x) (call 16 (cast-unsigned (word-width) x)))
(defun CALL16m (base scale index off seg) (call 16 (cast-unsigned (word-width) (load-n 16 (ea base scale index off seg)))))
(defun CALL32r (x) (call 32 (cast-unsigned (word-width) x)))
(defun CALL32m (base scale index off seg) (call 32 (cast-unsigned (word-width) (load-n 32 (ea base scale index off seg)))))
(defun CALL64r (x) (call 64 (cast-unsigned (word-width) x)))
(defun CALL64m (base scale index off seg) (call 64 (cast-unsigned (word-width) (load-n 64 (ea base scale index off seg)))))

;; RETI releases the bytes of the arguments after the return address
(defun release (n)
  (declare (context (bits 64)))
  (set RSP (+ RSP (cast-unsigned 64 (cast-low 16 n)))))

(defun release (n)
  (declare (context (bits 32)))
  (set ESP (+ ESP (cast-unsigned 32 (cast-low 16 n)))))

(defun RET16 () (exec-addr (cast-unsigned (word-width) (pop-n 16))))
(defun RETI16 (n) (let ((d (pop-n 16))) (release n) (exec-addr (cast-unsigned (word-width) d))))
(defun RET32 () (exec-addr (cast-unsigned (word-width) (pop-n 32))))
(defun RETI32 (n) (let ((d (pop-n 32))) (release n) (exec-addr (cast-unsigned (word-width) d))))
(defun RET64 () (exec-addr (cast-unsigned (word-width) (pop-n 64))))
(defun RETI64 (n) (let ((d (pop-n 64))) (release n) (exec-addr (cast-unsigned (word-width) d))))

;; the count register of LOOP and JCXZ has the size of the address
(defun JRCXZ (off) (declare (context (bits 64))) (when (is-zero RCX) (exec-addr (relative off))))
(defun JECXZ (off) (when (is-zero ECX) (exec-addr (relative off))))
(defun JCXZ (off) (when (is-zero CX) (exec-addr (relative off))))

;; with the address-size prefix the count is ECX, whose write clears the
;; upper half of RCX as any other of it does
(defun decrement-counter ()
  (declare (context (bits 64)))
  (if (x86-prefix 0x67)
      (let ((c (- ECX 1:32)))
        (set-ecx c)
        (non-zero c))
    (prog
     (set RCX (- RCX 1))
     (non-zero RCX))))

(defun decrement-counter ()
  (declare (context (bits 32)))
  (if (x86-prefix 0x67)
      (let ((c (- CX 1:16)))
        (set CX c)
        (non-zero c))
    (prog
     (set ECX (- ECX 1))
     (non-zero ECX))))

(defun LOOP (off) (when (decrement-counter) (exec-addr (relative off))))
(defun LOOPE (off)
  (let ((c (decrement-counter))) (when (logand c ZF) (exec-addr (relative off)))))
(defun LOOPNE (off)
  (let ((c (decrement-counter))) (when (logand c (not ZF)) (exec-addr (relative off)))))

;;; STRING INSTRUCTIONS
;;
;; DI and SI are the registers of the size of the address, they are
;; moved by the size of the operation, backward if DF is set. With the
;; REP prefix, 0xf3, the operation is repeated while the count register
;; is not zero, CMPS and SCAS also stop if ZF is clear, or with the REPNE
;; prefix, 0xf2, if ZF is set. The count register has the size of the
;; address, which the prefix 0x67 changes, and a 32-bit count clears the
;; upper half of RCX. Only the segment of the source may be overridden.

(defun string-step (r n)
  (set-gpr r (cast-low (word-width r) (if DF (- r (/ n 8)) (+ r (/ n 8))))))

(defun count-register ()
  (declare (context (bits 64)))
  (if (x86-prefix 0x67) ECX RCX))

(defun count-register ()
  (declare (context (bits 32)))
  (if (x86-prefix 0x67) CX ECX))

(defun set-count-register (x)
  (declare (context (bits 64)))
  (if (x86-prefix 0x67) (set-ecx (cast-low 32 x)) (set RCX x)))

(defun set-count-register (x)
  (declare (context (bits 32)))
  (if (x86-prefix 0x67) (set CX (cast-low 16 x)) (set ECX x)))

(defun repeated () (logor (x86-prefix 0xf3) (x86-prefix 0xf2)))

;; the condition of the repetitions of CMPS and SCAS
(defun continues ()
  (if (x86-prefix 0xf2) (not ZF) ZF))

;; A repeated instruction is one round of it: nothing with a count of
;; zero, else the body and the count, and then a jump to the instruction
;; itself while there is more to do. So what interrupts it, as a fault,
;; finds the registers and the memory of the rounds that completed, as of
;; the processor, and it goes on from there when it runs again. The count
;; of zero leaves first, so that nothing of the round is conditional but
;; the two jumps. What reads the code has the rounds as one loop, see
;; Disasm.Insn.asLoop.
(defmacro repeat (body)
  (if (repeated)
      (prog
       (when (is-zero (count-register)) (exec-addr (get-next-program-counter)))
       body
       (set-count-register (- (count-register) 1))
       (when (non-zero (count-register)) (exec-addr (get-program-counter))))
    body))

(defmacro repeat-while (body)
  (if (repeated)
      (prog
       (when (is-zero (count-register)) (exec-addr (get-next-program-counter)))
       body
       (set-count-register (- (count-register) 1))
       (when (logand (non-zero (count-register)) (continues)) (exec-addr (get-program-counter))))
    body))

;; the address of a register of the size of the address
(defun string-address (r) (cast-unsigned (word-width) r))

(defun movs (n di si seg)
  (repeat
   (prog
     (store-n n (string-address di) (load-n n (+ (segment-base seg) si)))
     (string-step di n)
     (string-step si n))))

(defun stos (n di x)
  (repeat (prog (store-n n (string-address di) x) (string-step di n))))

(defun cmps (n di si seg)
  (repeat-while
   (prog
     (sub-op (load-n n (+ (segment-base seg) si)) (load-n n (string-address di)))
     (string-step di n)
     (string-step si n))))

(defun scas (x n di)
  (repeat-while
   (prog
     (sub-op x (load-n n (string-address di)))
     (string-step di n))))

(defun MOVSB (di si seg) (movs 8 di si seg))
(defun MOVSW (di si seg) (movs 16 di si seg))
(defun MOVSL (di si seg) (movs 32 di si seg))
(defun MOVSQ (di si seg) (movs 64 di si seg))
(defun STOSB (di) (stos 8 di AL))
(defun STOSW (di) (stos 16 di AX))
(defun STOSL (di) (stos 32 di EAX))
(defun STOSQ (di) (declare (context (bits 64))) (stos 64 di RAX))
(defun CMPSB (di si seg) (cmps 8 di si seg))
(defun CMPSW (di si seg) (cmps 16 di si seg))
(defun CMPSL (di si seg) (cmps 32 di si seg))
(defun CMPSQ (di si seg) (cmps 64 di si seg))
(defun SCASB (di) (scas AL 8 di))
(defun SCASW (di) (scas AX 16 di))
(defun SCASL (di) (scas EAX 32 di))
(defun SCASQ (di) (declare (context (bits 64))) (scas RAX 64 di))

;; REP LODS loads as many times as the count says, so that nothing is
;; loaded with a count of zero, and only the last load stays
(defun lods (n si seg) (let ((x (load-n n (+ (segment-base seg) si)))) (string-step si n) x))
(defun LODSB (si seg) (repeat (set-al (lods 8 si seg))))
(defun LODSW (si seg) (repeat (set-ax (lods 16 si seg))))
(defun LODSL (si seg) (repeat (set-eax (lods 32 si seg))))
(defun LODSQ (si seg) (declare (context (bits 64))) (repeat (set-rax (lods 64 si seg))))

;;; THE FLAGS AND THE SYSTEM INSTRUCTIONS
;;
;; The instructions that access the processor or the system are calls
;; to the intrinsic functions, e.g., syscall, the barriers, the hints
;; and the prefetches have no effect.

(defun CLD () (set DF 0:1))
(defun STD () (set DF 1:1))
;; CLI and STI are of a program with the privilege of I/O, which one of
;; Linux hasn't unless it asked with iopl, which isn't modelled: a general
;; protection fault, as the other privileged instructions below are
(defun CLI () (x86-protection))
(defun STI () (x86-protection))

(defun CPUID ()
  (let ((r (intrinsic 'cpuid EAX ECX :result 128)))
    (set-eax (extract 31 0 r))
    (set-ebx (extract 63 32 r))
    (set-ecx (extract 95 64 r))
    (set-edx (extract 127 96 r))))

(defun RDTSC ()
  (let ((r (intrinsic 'rdtsc :result 64)))
    (set-edx (cast-high 32 r))
    (set-eax (cast-low 32 r))))

(defun RDTSCP ()
  (let ((r (intrinsic 'rdtscp :result 96)))
    (set-ecx (extract 95 64 r))
    (set-edx (extract 63 32 r))
    (set-eax (extract 31 0 r))))

;; XCR0, of the states that CPUID says the system keeps: x87, SSE, AVX,
;; and the masks and both halves of what AVX-512 adds; there is no other
;; extended control register
(defun XGETBV ()
  (if (= ECX 0:32)
      (prog (set-edx 0:32) (set-eax 0xe7:32))
    (x86-protection)))

;; What a program of Linux gets of the instructions that the processor
;; refuses it, each of which says so here:
;;
;; - a general protection fault, #GP, of what is privileged, and of INT
;;   to a gate that isn't of the program, is SIGSEGV of the kernel
;;   (exc_general_protection);
;; - INT 3 is the breakpoint, after its two bytes (exc_int3); INT 4 and
;;   INTO, the overflow trap, are SIGSEGV after the instruction
;;   (exc_overflow); INT1, the byte f1, is the debug trap (exc_debug);
;; - INT 0x80 is the system call of i386, which a process of 64 bits has
;;   by the compatibility entry (do_int80_emulation);
;; - what the processor doesn't have where the program runs is invalid,
;;   #UD, which is SIGILL: SYSENTER of an AMD in long mode, and the
;;   instructions of VMX, SVM, SMX and SGX outside of them.
(defun x86-protection () (intrinsic 'general-protection :aborts))

(defun INT (n)
  (let ((v (cast-low 8 n)))
    (if (= v 0x80:8) (x86-int80)
      (if (= v 3:8) (intrinsic 'interrupt-3 :aborts)
        (if (= v 4:8) (intrinsic 'interrupt-4 :aborts)
          (x86-protection))))))
(defun x86-int80 () (declare (context (bits 64))) (intrinsic 'syscall-compat))
(defun x86-int80 () (declare (context (bits 32))) (intrinsic 'interrupt 0x80:8))
(defun INT3 () (intrinsic 'breakpoint :aborts))
(defun INT1 () (intrinsic 'int1 :aborts))
(defun INTO () (when OF (intrinsic 'into :aborts)))
;; SYSCALL leaves where it returns to in RCX and the flags in R11, which is
;; of what serves the intrinsic, as it has all of the flags (the machine
;; of Linux does)
(defun SYSCALL () (intrinsic 'syscall))
(defun TRAP () (intrinsic '__ud2 :aborts))
(defun SYSENTER () (TRAP))
(defun SYSEXIT () (TRAP))
(defun SYSEXIT64 () (TRAP))

;; the ports
(defun IN8ri (_) (x86-protection))
(defun IN16ri (_) (x86-protection))
(defun IN32ri (_) (x86-protection))
(defun IN8rr () (x86-protection))
(defun IN16rr () (x86-protection))
(defun IN32rr () (x86-protection))
(defun OUT8ir (_) (x86-protection))
(defun OUT16ir (_) (x86-protection))
(defun OUT32ir (_) (x86-protection))
(defun OUT8rr () (x86-protection))
(defun OUT16rr () (x86-protection))
(defun OUT32rr () (x86-protection))
(defun INSB (_) (x86-protection))
(defun INSW (_) (x86-protection))
(defun INSL (_) (x86-protection))
(defun OUTSB (_ _) (x86-protection))
(defun OUTSW (_ _) (x86-protection))
(defun OUTSL (_ _) (x86-protection))
;; the registers of the system
(defun RDMSR () (x86-protection))
(defun WRMSR () (x86-protection))
(defun WRMSRNS () (x86-protection))
(defun RDMSRLIST () (x86-protection))
(defun WRMSRLIST () (x86-protection))
(defun RDPMC () (x86-protection))
(defun XSETBV () (x86-protection))
(defun MOV32rc (_ _) (x86-protection))
(defun MOV32cr (_ _) (x86-protection))
(defun MOV64rc (_ _) (x86-protection))
(defun MOV64cr (_ _) (x86-protection))
(defun MOV32rd (_ _) (x86-protection))
(defun MOV32dr (_ _) (x86-protection))
(defun MOV64rd (_ _) (x86-protection))
(defun MOV64dr (_ _) (x86-protection))
(defun CLTS () (x86-protection))
(defun LMSW16r (_) (x86-protection))
(defun LMSW16m (_ _ _ _ _) (x86-protection))
(defun INVD () (x86-protection))
(defun WBINVD () (x86-protection))
(defun WBNOINVD () (x86-protection))
(defun INVLPG (_ _ _ _ _) (x86-protection))
(defun INVPCID32 (_ _ _ _ _ _) (x86-protection))
(defun INVPCID64 (_ _ _ _ _ _) (x86-protection))
(defun SWAPGS () (x86-protection))
;; the tables of descriptors and the task
(defun LGDT16m (_ _ _ _ _) (x86-protection))
(defun LGDT32m (_ _ _ _ _) (x86-protection))
(defun LGDT64m (_ _ _ _ _) (x86-protection))
(defun LIDT16m (_ _ _ _ _) (x86-protection))
(defun LIDT32m (_ _ _ _ _) (x86-protection))
(defun LIDT64m (_ _ _ _ _) (x86-protection))
(defun LLDT16r (_) (x86-protection))
(defun LLDT16m (_ _ _ _ _) (x86-protection))
(defun LTRr (_) (x86-protection))
(defun LTRm (_ _ _ _ _) (x86-protection))
;; the returns of the kernel: IRET of a frame that a program made is
;; refused, as it is of the selectors it could have there but its own,
;; which isn't modelled
(defun IRET16 () (x86-protection))
(defun IRET32 () (x86-protection))
(defun IRET64 () (x86-protection))
(defun SYSRET () (x86-protection))
(defun SYSRET64 () (x86-protection))
;; what is invalid outside of a monitor or an enclave, or without the
;; extension, which the machine hasn't
(defun VMCALL () (TRAP))
(defun VMMCALL () (TRAP))
(defun VMLAUNCH () (TRAP))
(defun VMRESUME () (TRAP))
(defun VMXOFF () (TRAP))
(defun VMFUNC () (TRAP))
(defun VMRUN32 () (TRAP))
(defun VMRUN64 () (TRAP))
(defun VMLOAD32 () (TRAP))
(defun VMLOAD64 () (TRAP))
(defun VMSAVE32 () (TRAP))
(defun VMSAVE64 () (TRAP))
(defun STGI () (TRAP))
(defun CLGI () (TRAP))
(defun SKINIT () (TRAP))
(defun INVLPGA32 () (TRAP))
(defun INVLPGA64 () (TRAP))
(defun CLAC () (TRAP))
(defun STAC () (TRAP))
(defun ENCLS () (TRAP))
(defun ENCLU () (TRAP))
(defun ENCLV () (TRAP))
(defun GETSEC () (TRAP))
(defun RSM () (TRAP))
(defun VMXON (_ _ _ _ _) (TRAP))
(defun VMCLEARm (_ _ _ _ _) (TRAP))
(defun VMPTRLDm (_ _ _ _ _) (TRAP))
(defun VMPTRSTm (_ _ _ _ _) (TRAP))
(defun VMREAD32rr (_ _) (TRAP))
(defun VMREAD64rr (_ _) (TRAP))
(defun VMREAD32mr (_ _ _ _ _ _) (TRAP))
(defun VMREAD64mr (_ _ _ _ _ _) (TRAP))
(defun VMWRITE32rr (_ _) (TRAP))
(defun VMWRITE64rr (_ _) (TRAP))
(defun VMWRITE32rm (_ _ _ _ _ _) (TRAP))
(defun VMWRITE64rm (_ _ _ _ _ _) (TRAP))
(defun INVEPT32 (_ _ _ _ _ _) (TRAP))
(defun INVEPT64 (_ _ _ _ _ _) (TRAP))
(defun INVVPID32 (_ _ _ _ _ _) (TRAP))
(defun INVVPID64 (_ _ _ _ _ _) (TRAP))
(defun PCONFIG () (TRAP))
;; MONITOR and MWAIT are of the kernel, and invalid of a program
(defun MONITOR32rrr () (TRAP))
(defun MONITOR64rrr () (TRAP))
(defun MWAITrr () (TRAP))
(defun MONITORX32rrr () (TRAP))
(defun MONITORX64rrr () (TRAP))
(defun MWAITXrrr () (TRAP))
;; and what flushes the translations of other processors is privileged
(defun INVLPGB32 () (x86-protection))
(defun INVLPGB64 () (x86-protection))
(defun TLBSYNC () (x86-protection))

;; What a program may read of the system: the machine status word, the low
;; half of CR0 as Linux has it, PE, MP, ET, NE, WP, AM and PG, of which a
;; register of 32 or 64 bits has all; and the limit of a segment of the
;; kernel's table that it can see, which sets ZF, of 4 GiB, but that of
;; the segment that says which processor it is, of the first one.
(defun x86-msw () 0x80050033:32)
(defun SMSW16r (rd) (set$ rd (cast-low 16 (x86-msw))))
(defun SMSW32r (rd) (set-gpr rd (x86-msw)))
(defun SMSW64r (rd) (set$ rd (cast-unsigned 64 (x86-msw))))
(defun SMSW16m (b s i off seg) (store-n 16 (ea b s i off seg) (x86-msw)))

;; A selector that a program of 64 bits may load: a null one, or one of
;; the kernel's table that is its own: the code and the data of 32 bits,
;; 4 and 5, the code of 64, 6, and the segment of the processor's number,
;; 15. The stack takes its own data segment only.
(defun x86-selector-seen (sel)
  (let ((index (rshift sel 3)))
    (logand (not (extract 2 2 sel))
            (logor (= index 4) (= index 5) (= index 6) (= index 15)))))
(defun x86-selector-loads (stack sel)
  (if stack (= sel 0x2b:16)
    (logor (< sel 4:16) (x86-selector-seen sel))))
(defun x86-load-selector (s x)
  (declare (context (bits 64)))
  (let ((sel (cast-low 16 x)))
    (if (= (symbol s) 'CS) (TRAP)
      (if (x86-selector-loads (= (symbol s) 'SS) sel) (set$ s sel) (x86-protection)))))
(defun x86-load-selector (s x)
  (declare (context (bits 32)))
  (if (= (symbol s) 'CS) (TRAP) (set$ s (cast-low 16 x))))

;; The other things of the tables that a program may read, of a processor
;; without UMIP, as CPUID says this one is: there is no local table, the
;; task register is the kernel's, entry 8; the tables are where Linux has
;; them of the first processor, in its fixed mappings; and the access rights
;; of a segment that the program can see are its type, its privilege and its
;; flags: code of 32 and of 64 bits, data, and the read-only segment of the
;; processor's number. VERR and VERW say whether one can be read or written.
(defun SLDT16r (rd) (set$ rd 0:16))
(defun SLDT32r (rd) (set-gpr rd 0:32))
(defun SLDT64r (rd) (set$ rd 0:64))
(defun SLDT16m (b s i off seg) (store-n 16 (ea b s i off seg) 0:16))
(defun STR16r (rd) (set$ rd 0x40:16))
(defun STR32r (rd) (set-gpr rd 0x40:32))
(defun STR64r (rd) (set$ rd 0x40:64))
(defun STRm (b s i off seg) (store-n 16 (ea b s i off seg) 0x40:16))
(defun x86-store-table (wide a limit base)
  (store-n 16 a limit)
  (store-n wide (+ a 2) base))
(defun SGDT64m (b s i off seg) (x86-store-table 64 (ea b s i off seg) 0x7f:16 0xfffffe0000001000:64))
(defun SIDT64m (b s i off seg) (x86-store-table 64 (ea b s i off seg) 0xfff:16 0xfffffe0000000000:64))
(defun SGDT32m (b s i off seg) (x86-store-table 32 (ea b s i off seg) 0x7f:16 0x00001000:32))
(defun SIDT32m (b s i off seg) (x86-store-table 32 (ea b s i off seg) 0xfff:16 0x00000000:32))
(defun SGDT16m (b s i off seg) (x86-store-table 32 (ea b s i off seg) 0x7f:16 0x00001000:32))
(defun SIDT16m (b s i off seg) (x86-store-table 32 (ea b s i off seg) 0xfff:16 0x00000000:32))

(defun x86-access-rights (sel)
  (let ((index (rshift sel 3)))
    (if (= index 4:16) 0x00cffb00:32
      (if (= index 5:16) 0x00cff300:32
        (if (= index 6:16) 0x00affb00:32 0x0040f500:32)))))
(defun x86-lar (rd x)
  (let ((sel (cast-low 16 x)))
    (if (x86-selector-seen sel)
        (prog (set ZF 1:1)
              (set-gpr rd (resize (word-width rd) (x86-access-rights sel))))
      (set ZF 0:1))))
(defun LAR16rr (rd x) (x86-lar rd x))
(defun LAR32rr (rd x) (x86-lar rd x))
(defun LAR64rr (rd x) (x86-lar rd x))
(defun LAR16rm (rd b s i off seg) (x86-lar rd (load-n 16 (ea b s i off seg))))
(defun LAR32rm (rd b s i off seg) (x86-lar rd (load-n 16 (ea b s i off seg))))
(defun LAR64rm (rd b s i off seg) (x86-lar rd (load-n 16 (ea b s i off seg))))
(defun x86-verr (x) (set ZF (x86-selector-seen (cast-low 16 x))))
(defun x86-verw (x)
  (let ((sel (cast-low 16 x)))
    (set ZF (logand (x86-selector-seen sel) (= (rshift sel 3) 5:16)))))
(defun VERRr (x) (x86-verr x))
(defun VERRm (b s i off seg) (x86-verr (load-n 16 (ea b s i off seg))))
(defun VERWr (x) (x86-verw x))
(defun VERWm (b s i off seg) (x86-verw (load-n 16 (ea b s i off seg))))

(defun x86-lsl (rd x)
  (let ((sel (cast-low 16 x)))
    (if (x86-selector-seen sel)
        (prog (set ZF 1:1)
              (set-gpr rd (if (= (rshift sel 3) 15:16) (cast-unsigned (word-width rd) 0:1) (cast-low (word-width rd) 0xffffffff:64))))
      (set ZF 0:1))))
(defun LSL16rr (rd x) (x86-lsl rd x))
(defun LSL32rr (rd x) (x86-lsl rd x))
(defun LSL64rr (rd x) (x86-lsl rd x))
(defun LSL16rm (rd b s i off seg) (x86-lsl rd (load-n 16 (ea b s i off seg))))
(defun LSL32rm (rd b s i off seg) (x86-lsl rd (load-n 16 (ea b s i off seg))))
(defun LSL64rm (rd b s i off seg) (x86-lsl rd (load-n 16 (ea b s i off seg))))

;; The extensions, that the processor of Unicorn doesn't have, see its
;; CPUID, whose instructions are invalid, as on such a processor: the
;; shadow stacks of CET, but RDSSP and INCSSP, which are NOPs there, as
;; the shadow stack is disabled, the transactions of TSX, and the
;; protection keys.
(defun RDSSPD (_ _) (empty))
(defun RDSSPQ (_ _) (empty))
(defun INCSSPD (_) (empty))
(defun INCSSPQ (_) (empty))
(defun RSTORSSP (_ _ _ _ _) (TRAP))
(defun SAVEPREVSSP () (TRAP))
(defun SETSSBSY () (TRAP))
(defun CLRSSBSY (_ _ _ _ _) (TRAP))
(defun WRSSD (_ _ _ _ _ _) (TRAP))
(defun WRSSQ (_ _ _ _ _ _) (TRAP))
(defun WRUSSD (_ _ _ _ _ _) (TRAP))
(defun WRUSSQ (_ _ _ _ _ _) (TRAP))
(defun XTEST () (TRAP))
(defun RDPKRUr () (TRAP))
(defun WRPKRUr () (TRAP))

;; ENDBR are calls to the endbr intrinsic if --x86-cet-enabled
(defun ENDBR32 () (empty))
(defun ENDBR64 () (empty))
(defun ENDBR32 () (declare (context (x86-cet enabled))) (intrinsic 'endbr))
(defun ENDBR64 () (declare (context (x86-cet enabled))) (intrinsic 'endbr))

(defun PAUSE () (empty))
(defun LFENCE () (empty))
(defun SFENCE () (empty))
(defun WAIT () (x87-wait))
(defun PREFETCH (_ _ _ _ _) (empty))
(defun PREFETCHW (_ _ _ _ _) (empty))
(defun PREFETCHT0 (_ _ _ _ _) (empty))
(defun PREFETCHT1 (_ _ _ _ _) (empty))
(defun PREFETCHT2 (_ _ _ _ _) (empty))
(defun PREFETCHNTA (_ _ _ _ _) (empty))
(defun CLFLUSH (_ _ _ _ _) (empty))
(defun CLFLUSHOPT (_ _ _ _ _) (empty))

(defun STMXCSR (base scale index off seg) (store-n 32 (ea base scale index off seg) MXCSR))
(defun LDMXCSR (base scale index off seg) (set MXCSR (load-n 32 (ea base scale index off seg))))
(defun VSTMXCSR (base scale index off seg) (store-n 32 (ea base scale index off seg) MXCSR))
(defun VLDMXCSR (base scale index off seg) (set MXCSR (load-n 32 (ea base scale index off seg))))
(defun FNSTCW16m (base scale index off seg) (store-n 16 (ea base scale index off seg) FPU_CONTROL))
(defun FLDCW16m (base scale index off seg) (x87-wait) (set FPU_CONTROL (load-n 16 (ea base scale index off seg))) (x87-summarize))

