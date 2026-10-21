(defparameter *patched* nil)

(defmethod call (name c)
  (when (and (= name 'putchar) (not *patched*))
    (set *patched* true)
    (memory-allocate 0x8000 0x1000)
    (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write (memory-write
        0x8000 0x00:8) 0xb5:8) 0x00:8) 0xf0:8) 0x7e:8) 0xe8:8) 0x18:8) 0xf0:8)
        0x8c:8) 0xe9:8) 0x00:8) 0xbd:8)
    (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write (memory-write (memory-write
        0x8100 0x2b:8) 0x00:8) 0xa0:8) 0xe3:8) 0x1e:8) 0xff:8) 0x2f:8) 0xe1:8)
    (memory-protect 0x8000 0x1000 5)
    (memory-protect 0x202d0 6 7)
    (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write 0x202d0 0x48:8) 0xf2:8) 0x01:8) 0x03:8) 0x98:8) 0x47:8)
    (memory-protect 0x202d0 6 5)))
