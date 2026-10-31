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

(defun decrement-counter ()
  (declare (context (bits 64)))
  (set RCX (- RCX 1))
  (non-zero RCX))

(defun decrement-counter ()
  (declare (context (bits 32)))
  (set ECX (- ECX 1))
  (non-zero ECX))

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

(defmacro repeat (body)
  (if (repeated)
      (while (non-zero (count-register))
        body
        (set-count-register (- (count-register) 1)))
    body))

(defmacro repeat-while (body)
  (if (repeated)
      (let ((go true))
        (while (logand go (non-zero (count-register)))
          body
          (set-count-register (- (count-register) 1))
          (set go (continues))))
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

;; LODS is not repeated, as only the last load would matter
(defun lods (n si seg) (let ((x (load-n n (+ (segment-base seg) si)))) (string-step si n) x))
(defun LODSB (si seg) (set-al (lods 8 si seg)))
(defun LODSW (si seg) (set-ax (lods 16 si seg)))
(defun LODSL (si seg) (set-eax (lods 32 si seg)))
(defun LODSQ (si seg) (declare (context (bits 64))) (set-rax (lods 64 si seg)))

;;; THE FLAGS AND THE SYSTEM INSTRUCTIONS
;;
;; The instructions that access the processor or the system are calls
;; to the intrinsic functions, e.g., syscall, the barriers, the hints
;; and the prefetches have no effect.

(defun CLD () (set DF 0:1))
(defun STD () (set DF 1:1))
(defun CLI () (set IF 0:1))
(defun STI () (set IF 1:1))

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

(defun XGETBV ()
  (let ((r (intrinsic 'xgetbv ECX :result 64)))
    (set-edx (cast-high 32 r))
    (set-eax (cast-low 32 r))))

(defun INT (n) (intrinsic 'interrupt (cast-low 8 n)))
(defun INT3 () (intrinsic 'breakpoint :aborts))
(defun SYSCALL () (intrinsic 'syscall))
(defun SYSENTER () (intrinsic 'sysenter))
(defun TRAP () (intrinsic '__ud2 :aborts))

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
(defun WAIT () (empty))
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
(defun FLDCW16m (base scale index off seg) (set FPU_CONTROL (load-n 16 (ea base scale index off seg))))

