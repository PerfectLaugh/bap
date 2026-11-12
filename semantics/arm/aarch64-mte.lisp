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
;; and nothing is checked. What they do of the address, and of the data
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

;; what is read of a tag is 0, which LDG puts in the address it is given

(defun LDG (rt _ rn off) (set$ rt (mte-with-tag rt 0)))

;; what is written of a tag is ignored; what is zeroed is zeroed, and what
;; is written back of the base is as of the stores of the same forms

(defun STGi (_ rn off) (empty))
(defun STGPreIndex (wb _ rn off) (set$ wb (+ rn (* off (mte-granule)))))
(defun STGPostIndex (wb _ rn off) (set$ wb (+ rn (* off (mte-granule)))))
(defun ST2Gi (_ rn off) (empty))
(defun ST2GPreIndex (wb _ rn off) (set$ wb (+ rn (* off (mte-granule)))))
(defun ST2GPostIndex (wb _ rn off) (set$ wb (+ rn (* off (mte-granule)))))

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
