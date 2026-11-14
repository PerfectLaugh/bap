(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

(require bits)
(require arm-bits)
(require aarch64-helper)
(require aarch64-special)

;;; THE MEMORY TAGGING EXTENSION (MTE)
;;
;; As Linux has it for a process that hasn't asked for tags: no memory is
;; mapped with PROT_MTE, so that the allocation tags of all of it read as
;; zero and what is written of them is ignored (RAZ/WI), and every tag is
;; excluded, as GCR_EL1 is until PR_SET_TAGGED_ADDR_CTRL includes some,
;; which the machine doesn't take. So IRG, ADDG and SUBG make the tag 0,
;; and no tag is checked. What they do of the address, and of the data
;; that STZG, STZ2G and STGP write, is as the Arm ARM has it. LDGM, STGM
;; and STZGM are of EL1, and undefined here.

(defun mte-granule () 16)

(defun mte-with-tag (x tag)
  "X with the allocation tag of an address, its bits 56 to 59, as TAG"
  (logor (logand x (lnot (lshift (cast-unsigned 64 0xf) 56)))
         (lshift (cast-unsigned 64 tag) 56)))

(defun mte-tag-of (x) (cast-unsigned 64 (extract 59 56 x)))

(defun mte-address56 (x)
  "the bits 0 to 55 of X, extended by its sign, as SUBP and SUBPS take them"
  (cast-signed 64 (cast-low 56 x)))

(defun mte-addg (rd rn offset subtract)
  "ADDG and SUBG: the address moved by OFFSET bytes, as AddressAdd moves it,
   of the tag that ChooseNonExcludedTag gives, which is 0 as all are excluded"
  (let ((a (if subtract (- rn (cast-unsigned 64 offset)) (+ rn (cast-unsigned 64 offset)))))
    (set$ rd (mte-with-tag a 0))))

(defun mte-zero-granules (address count)
  "zeros COUNT granules from the granule of ADDRESS"
  (let ((a (logand address (lnot (cast-unsigned 64 15)))))
    (store-word a (cast-unsigned (* count 128) 0))))

;; the tags

(defun IRG (rd rn rm) (set$ rd (mte-with-tag rn 0)))
(defun ADDG (rd rn offset tag) (mte-addg rd rn (* offset (mte-granule)) false))
(defun SUBG (rd rn offset tag) (mte-addg rd rn (* offset (mte-granule)) true))
(defun GMI (rd rn rm) (set$ rd (logor rm (lshift (cast-unsigned 64 1) (mte-tag-of rn)))))
(defun SUBP (rd rn rm) (set$ rd (- (mte-address56 rn) (mte-address56 rm))))
(defun SUBPS (rd rn rm)
  (let ((a (mte-address56 rn)) (b (mte-address56 rm)))
    (add-with-carry rd a (lnot b) (cast-unsigned 64 1))))

;; An access of tags is translated as one of the memory it is of, so
;; that it faults where that would, though what it reads is 0 and what it
;; writes is ignored: LDG reads a byte of the granule, and STG and ST2G
;; write the bytes of their granules back as they are, which faults of
;; memory that can't be written. The alignment of the address isn't checked.

(defun mte-probe-read (address)
  "0, of a read of the granule of ADDRESS, which the result depends on, so
   that the read isn't dropped as dead"
  (let ((a (logand address (lnot (cast-unsigned 64 15)))))
    (if (= (cast-unsigned 16 (load-bits 8 a)) (cast-unsigned 16 256)) 1 0)))

(defun mte-probe-write (address count)
  "writes the first byte of each of COUNT granules from that of ADDRESS as
   it is"
  (let ((a (logand address (lnot (cast-unsigned 64 15)))))
    (store-byte a (load-bits 8 a))
    (when (> count 1) (mte-probe-write (+ a 16) (- count 1)))))

;; what is read of a tag is 0, which LDG puts in the address it is given

(defun LDG (rt _ rn off)
  (let ((tag (mte-probe-read (+ rn (* off (mte-granule))))))
    (set$ rt (mte-with-tag rt tag))))

;; what is written of a tag is ignored; what is zeroed is zeroed, and what
;; is written back of the base is as of the stores of the same forms

(defun STGi (_ rn off) (mte-probe-write (+ rn (* off (mte-granule))) 1))
(defun STGPreIndex (wb _ rn off)
  (let ((a (+ rn (* off (mte-granule)))))
    (mte-probe-write a 1)
    (set$ wb a)))
(defun STGPostIndex (wb _ rn off)
  (mte-probe-write rn 1)
  (set$ wb (+ rn (* off (mte-granule)))))
(defun ST2Gi (_ rn off) (mte-probe-write (+ rn (* off (mte-granule))) 2))
(defun ST2GPreIndex (wb _ rn off)
  (let ((a (+ rn (* off (mte-granule)))))
    (mte-probe-write a 2)
    (set$ wb a)))
(defun ST2GPostIndex (wb _ rn off)
  (mte-probe-write rn 2)
  (set$ wb (+ rn (* off (mte-granule)))))

(defun STZGi (_ rn off) (mte-zero-granules (+ rn (* off (mte-granule))) 1))
(defun STZGPreIndex (wb _ rn off)
  (let ((a (+ rn (* off (mte-granule)))))
    (mte-zero-granules a 1)
    (set$ wb a)))
(defun STZGPostIndex (wb _ rn off)
  (let ((a rn))
    (mte-zero-granules a 1)
    (set$ wb (+ a (* off (mte-granule))))))
(defun STZ2Gi (_ rn off) (mte-zero-granules (+ rn (* off (mte-granule))) 2))
(defun STZ2GPreIndex (wb _ rn off)
  (let ((a (+ rn (* off (mte-granule)))))
    (mte-zero-granules a 2)
    (set$ wb a)))
(defun STZ2GPostIndex (wb _ rn off)
  (let ((a rn))
    (mte-zero-granules a 2)
    (set$ wb (+ a (* off (mte-granule))))))

(defun STGPi (t1 t2 rn off)
  (let ((a (+ rn (* off (mte-granule)))))
    (store-word a t1)
    (store-word (+ a 8) t2)))
(defun STGPpre (wb t1 t2 rn off)
  (let ((a (+ rn (* off (mte-granule)))))
    (store-word a t1)
    (store-word (+ a 8) t2)
    (set$ wb a)))
(defun STGPpost (wb t1 t2 rn off)
  (let ((a rn))
    (store-word a t1)
    (store-word (+ a 8) t2)
    (set$ wb (+ a (* off (mte-granule))))))

;; of EL1
(defun LDGM (rt rn) (a64-undefined))
(defun STGM (rt rn) (a64-undefined))
(defun STZGM (rt rn) (a64-undefined))
