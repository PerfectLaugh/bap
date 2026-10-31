(declare (context (target amd64) (bits 64)))
(require x86-common)

(defpackage x86-64 (:use core target amd64 x86_64))
(defpackage llvm-x86_64 (:use x86_64))

(in-package x86-64)
