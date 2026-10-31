(declare (context (target x86)))
(require x86-common)

(in-package x86-common)

;;; AMX: THE TILE REGISTERS
;;
;; A tile is TMM0 ... TMM7, of 16 rows of 64 bytes, the first row in its low
;; bits, and TILECFG is the 64 bytes of the configuration that LDTILECFG
;; loads: the palette in byte 0, the bytes of the columns of each tile as
;; words from byte 16, and the rows of each tile from byte 48. All these
;; registers are outside of the BIL of other instructions, and only these
;; instructions see them.
;;
;; `x86ExpandOperands` of `Bap.Target.LLVMLift` gives a tile operand as the
;; register and its number, as how many rows and columns it has is by the number.
;; An instruction only reads the rows and the columns that the configuration has for its
;; tile, and clears the others. What isn't modeled is the palette's limits:
;; a configuration that faults on the machine is run as if it didn't, and the
;; start row that a restart after a page fault uses isn't kept.

(defun tile-byte-of (name k) (extract (+ (* 8 k) 7) (* 8 k) name))

(defun tile-rows (t) (cast-unsigned 64 (tile-byte-of TILECFG (+ 48 t))))
(defun tile-colsb (t)
  (concat (cast-unsigned 56 (tile-byte-of TILECFG (+ 17 (* 2 t)))) (tile-byte-of TILECFG (+ 16 (* 2 t)))))

(defun tile-offset (m n e) (+ (* m 512) (* n e)))
(defun tile-element (e v m n) (cast-low e (rshift v (tile-offset m n e))))
(defun tile-place (e x m n) (lshift (cast-unsigned 8192 (cast-low e x)) (tile-offset m n e)))

(defun tile-clear-all ()
  (set$ TMM0 (zeros 8192)) (set$ TMM1 (zeros 8192)) (set$ TMM2 (zeros 8192)) (set$ TMM3 (zeros 8192))
  (set$ TMM4 (zeros 8192)) (set$ TMM5 (zeros 8192)) (set$ TMM6 (zeros 8192)) (set$ TMM7 (zeros 8192)))

(defun LDTILECFG (b s i off seg)
  (set$ TILECFG (load-n 512 (ea b s i off seg)))
  (tile-clear-all))
(defun STTILECFG (b s i off seg) (store-n 512 (ea b s i off seg) TILECFG))
(defun TILERELEASE ()
  (set$ TILECFG (zeros 512))
  (tile-clear-all))
(defun TILEZERO (rd _) (set$ rd (zeros 8192)))

;; the loads and the stores: a row is at START + M * STRIDE, the base with
;; the offset and the index with the scale, of the bytes that it has

(defun tile-start (b off seg) (ea b 1 'Nil off seg))
(defun tile-stride (s i) (operand-address 'Nil s i 0))

(defun tile-load (rd t b s i off seg)
  (let ((start (tile-start b off seg))
        (stride (tile-stride s i))
        (rows (tile-rows t))
        (cols (tile-colsb t))
        (out (zeros 8192))
        (m 0:64))
    (while (< m rows)
      (let ((n 0:64))
        (while (< n cols)
          (set out (logor out (tile-place 8 (load-n 8 (+ start (* m stride) n)) m n)))
          (set n (+ n 1:64))))
      (set m (+ m 1:64)))
    (set$ rd out)))

(defun TILELOADD (rd t b s i off seg) (tile-load rd t b s i off seg))
(defun TILELOADDT1 (rd t b s i off seg) (tile-load rd t b s i off seg))
(defun TILELOADDRS (rd t b s i off seg) (tile-load rd t b s i off seg))
(defun TILELOADDRST1 (rd t b s i off seg) (tile-load rd t b s i off seg))

(defun TILESTORED (b s i off seg x t)
  (let ((start (tile-start b off seg))
        (stride (tile-stride s i))
        (rows (tile-rows t))
        (cols (tile-colsb t))
        (m 0:64))
    (while (< m rows)
      (let ((n 0:64))
        (while (< n cols)
          (store-n 8 (+ start (* m stride) n) (tile-element 8 x m n))
          (set n (+ n 1:64))))
      (set m (+ m 1:64)))))

;; the dot products: each dword of the destination has the sum, over the
;; dwords of a row of the first source, of the four products of its bytes
;; with those of a dword of the row of the second source that its number says

(defun tile-dot (sx sy rd t pass a ta b)
  (let ((rows (tile-rows t))
        (cols (/ (tile-colsb t) 4:64))
        (terms (/ (tile-colsb ta) 4:64))
        (out (zeros 8192))
        (m 0:64))
    (while (< m rows)
      (let ((n 0:64))
        (while (< n cols)
          (let ((sum (tile-element 32 pass m n))
                (k 0:64))
            (while (< k terms)
              (set sum (+ sum (cast-low 32 (evex-dot8 sx sy (tile-element 32 a m k) (tile-element 32 b k n)))))
              (set k (+ k 1:64)))
            (set out (logor out (tile-place 32 sum m n))))
          (set n (+ n 1:64))))
      (set m (+ m 1:64)))
    (set$ rd out)))

(defun TDPBSSD (rd t pass _ a ta b _) (tile-dot true true rd t pass a ta b))
(defun TDPBSUD (rd t pass _ a ta b _) (tile-dot true false rd t pass a ta b))
(defun TDPBUSD (rd t pass _ a ta b _) (tile-dot false true rd t pass a ta b))
(defun TDPBUUD (rd t pass _ a ta b _) (tile-dot false false rd t pass a ta b))

;; those of floats, which are intrinsics of the whole of the tiles, with the sizes that they use

(defun tile-float (name rd t pass a ta b tb)
  (set$ rd (intrinsic name pass a b (tile-rows t) (tile-colsb t) (tile-rows ta) (tile-colsb ta) (tile-rows tb) (tile-colsb tb) :result 8192)))

(defun TDPBF16PS (rd t pass _ a ta b tb) (tile-float 'tdpbf16ps rd t pass a ta b tb))
(defun TDPFP16PS (rd t pass _ a ta b tb) (tile-float 'tdpfp16ps rd t pass a ta b tb))
(defun TCMMIMFP16PS (rd t pass _ a ta b tb) (tile-float 'tcmmimfp16ps rd t pass a ta b tb))
(defun TCMMRLFP16PS (rd t pass _ a ta b tb) (tile-float 'tcmmrlfp16ps rd t pass a ta b tb))
(defun TDPBF8PS (rd t pass _ a ta b tb) (tile-float 'tdpbf8ps rd t pass a ta b tb))
(defun TDPBHF8PS (rd t pass _ a ta b tb) (tile-float 'tdpbhf8ps rd t pass a ta b tb))
(defun TDPHBF8PS (rd t pass _ a ta b tb) (tile-float 'tdphbf8ps rd t pass a ta b tb))
(defun TDPHF8PS (rd t pass _ a ta b tb) (tile-float 'tdphf8ps rd t pass a ta b tb))

;; a row of a tile to a ZMM register, by the low 4 bits of a register or
;; an immediate. A row that the tile doesn't have is zero, and so is a
;; byte past the columns that it has

(defun tile-row (x t r)
  (let ((m (logand (cast-unsigned 64 r) 15:64)))
    (if (< m (tile-rows t))
        (cast-low 512 (rshift x (* m 512:64)))
      (zeros 512))))

(defun tile-lane-byte (row cols _ _ _ _ _ i)
  (if (< i cols) (evex-lane 8 row i) 0:8))

(defun tile-move-row (rd x t r)
  (let ((row (tile-row x t r))
        (cols (tile-colsb t)))
    (set-vex rd (evex-lanes 0 0 0 8 tile-lane-byte row cols 0 0 0 0 0 0 64))))

(defun TILEMOVROWrti (rd x t r) (tile-move-row rd x t r))
(defun TILEMOVROWrte (rd x t r) (tile-move-row rd x t r))

;; the conversions of a row, whose rounding mode is RNE, of which the half
;; that isn't converted to is clear

(defun tile-to-float (x) (sse-convert 'cast_sfloat 'rne 32 32 x))
(defun tile-to-half (x) (sse-convert 'fconvert 'rne 32 16 x))
(defun tile-to-bf16 (x) (intrinsic 'fconvert_rne_bfloat_32_16 (cast-low 32 x) :result 16))

(defun tile-lane-float (row cols _ _ _ _ _ i)
  (if (< i (/ cols 4:64)) (tile-to-float (evex-lane 32 row i)) 0:32))
(defun tile-lane-high (f row cols _ _ _ _ i)
  (if (< i (/ cols 4:64)) (concat (f (evex-lane 32 row i)) 0:16) 0:32))
(defun tile-lane-low (f row cols _ _ _ _ i)
  (if (< i (/ cols 4:64)) (concat 0:16 (f (evex-lane 32 row i))) 0:32))

(defun tile-row-to-float (rd x t r)
  (let ((row (tile-row x t r))
        (cols (tile-colsb t)))
    (set-vex rd (evex-lanes 0 0 0 32 tile-lane-float row cols 0 0 0 0 0 0 16))))
(defun tile-row-half (lane f rd x t r)
  (let ((row (tile-row x t r))
        (cols (tile-colsb t)))
    (set-vex rd (evex-lanes 0 0 0 32 lane f row cols 0 0 0 0 0 16))))

(defun TCVTROWD2PSrti (rd x t r) (tile-row-to-float rd x t r))
(defun TCVTROWD2PSrte (rd x t r) (tile-row-to-float rd x t r))
(defun TCVTROWPS2PHHrti (rd x t r) (tile-row-half tile-lane-high tile-to-half rd x t r))
(defun TCVTROWPS2PHHrte (rd x t r) (tile-row-half tile-lane-high tile-to-half rd x t r))
(defun TCVTROWPS2PHLrti (rd x t r) (tile-row-half tile-lane-low tile-to-half rd x t r))
(defun TCVTROWPS2PHLrte (rd x t r) (tile-row-half tile-lane-low tile-to-half rd x t r))
(defun TCVTROWPS2BF16Hrti (rd x t r) (tile-row-half tile-lane-high tile-to-bf16 rd x t r))
(defun TCVTROWPS2BF16Hrte (rd x t r) (tile-row-half tile-lane-high tile-to-bf16 rd x t r))
(defun TCVTROWPS2BF16Lrti (rd x t r) (tile-row-half tile-lane-low tile-to-bf16 rd x t r))
(defun TCVTROWPS2BF16Lrte (rd x t r) (tile-row-half tile-lane-low tile-to-bf16 rd x t r))

;;; CMPCCXADD

;; The comparison of the word of memory with the register sets the flags;
;; under the condition of them, the third operand is added to the memory.
;; The memory is always written, and the register always gets its old value.

(defun cmpccxadd (rd x b s i off seg y cc)
  (let ((a (ea b s i off seg))
        (old (load-n (word-width y) a)))
    (sub-op old x)
    (store-n (word-width y) a (if (condition cc) (+ old y) old))
    (set-gpr rd old)))

(defun CMPCCXADDmr32 (rd x b s i off seg y cc) (cmpccxadd rd x b s i off seg y cc))
(defun CMPCCXADDmr64 (rd x b s i off seg y cc) (cmpccxadd rd x b s i off seg y cc))
