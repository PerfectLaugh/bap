(require libc-init)
(require memory)
(require types)

(in-package posix)

(defun fputc (char stream)
  (declare (external "fputc" "putc" "fputs_unlocked putc_unlocked"))
  (if (= 0 (channel-output stream char)) char -1))

(defun putchar (char)
  (declare (external "putchar" "putchar_unlocked"))
  (fputc char *standard-output*))

(defun fputs (p stream)
  (declare (external "fputs" "fputs_unlocked"))
  (while (not (points-to-null p))
    (fputc (cast int (memory-read p)) stream)
    (incr p))
  (let ((r (fputc 0xA stream)))
    (fflush stream)
    r))

(defun puts (p)
  (declare (external "puts" "puts_unlocked"))
  (fputs p *standard-output*))

;; the functions of the printf family take the words, that the C ABI
;; passes after the format, at most eight of them, see channel-printf
(defun printf (fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "printf"))
  (channel-printf *standard-output* fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun printf-chk (flag fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "__printf_chk"))
  (channel-printf *standard-output* fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun fprintf (stream fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "fprintf" "dprintf"))
  (channel-printf stream fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun fprintf-chk (stream flag fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "__fprintf_chk"))
  (channel-printf stream fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun sprintf (buf fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "sprintf"))
  (memory-printf buf -1 fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun sprintf-chk (buf flag len fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "__sprintf_chk"))
  (memory-printf buf -1 fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun snprintf (buf size fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "snprintf"))
  (memory-printf buf size fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun snprintf-chk (buf size flag len fmt a0 a1 a2 a3 a4 a5 a6 a7)
  (declare (external "__snprintf_chk"))
  (memory-printf buf size fmt a0 a1 a2 a3 a4 a5 a6 a7))

(defun fflush (s)
  (declare (external "fflush" "fflush_unlocked"))
  (channel-flush s))



;; the channel module have rough equality between streams and
;; file descriptors, as they both are represented as integers. We are currently
;; ignoring modes, we will add them later, of course.
(defun fopen (path mode)
  (declare (external "fopen" "fdopen"))
  (let ((file (channel-open path)))
    (if (is-negative file) 0 file)))

(defun close (fd)
  "flushes and closes the channel, -1 if it isn't open"
  (declare (external "close" "fclose"))
  (channel-flush fd)
  (channel-close fd))

(defun fseek (stream off whence)
  "moves the position of the channel, which it reads, 0 on success"
  (declare (external "fseek" "fseeko"))
  (channel-seek stream off whence))

(defun ftell (stream)
  "the position of the channel, which it reads, or -1"
  (declare (external "ftell" "ftello"))
  (channel-position stream))

(defun rewind (stream)
  (declare (external "rewind"))
  (channel-seek stream 0 0)
  0)

(defun lseek (fd off whence)
  "moves the position of the channel, which it reads, and returns it,
   or -1"
  (declare (external "lseek" "lseek64"))
  (if (= 0 (channel-seek fd off whence))
      (channel-position fd)
    -1))

(defun fileno (stream)
  (declare (external "fileno"))
  stream)

(defun open2 (path flags)
  "the descriptor of the file, that is redirected, or -1, rather than
   the null of fopen, which is the descriptor of the standard input"
  (declare (external "open"))
  (let ((fd (channel-open path)))
    (if (is-negative fd) -1 fd)))

(defun open3 (path flags mode)
  (declare (external "open"))
  (open2 path flags))

(defun output-item-nth-char (ptr size item fd i)
  (= 0 (channel-output
        fd
        (memory-read (+ ptr (* size item) i)))))

(defun output-item (buf size item fd)
  (let ((i 0))
    (while (and
            (< i size)
            (output-item-nth-char buf size item fd i))
      (incr i))
    i))

(defun fwrite (buf size n stream)
  (declare (external "fwrite" "fwrite_unlocked"))
  (let ((i 0))
    (while (and (< i n)
                (= size (output-item buf size i stream)))
      (incr i))
    i))

(defun write (fd buf cnt)
  (declare (external "write"))
  (let ((written (fwrite buf 1 cnt fd))
        (failure (channel-flush fd)))
    (or failure written)))

(defun input-item-nth-char (ptr size item desc i)
  (declare (visibility :private))
  (let ((c (fgetc desc)))
    (if (= c -1) 0
        (memory-write (+ ptr (* size item) i) (cast char c))
        1)))

(defun input-item (buf size item fd)
  (declare (visibility :private))
  (let ((i 0))
    (while (and (< i size)
                (input-item-nth-char buf size item fd i))
      (incr i))
    i))

(defun fread (ptr size n stream)
  (declare (external "fread" "fread_unlocked"))
  (let ((i 0))
    (while (and
            (< i n)
            (= size (input-item ptr size i stream)))
      (incr i))
    i))

(defun read (fd buf n)
  (declare (external "read"))
  (fread buf 1 n fd))


(defun fgetc (stream)
  (declare (external "fgetc" "getc" "fgetc_unlocked" "getc_unlocked"))
  (channel-input stream))

(defun terminate-string-and-return-null (ptr)
  (declare (visibility :private))
  (memory-write ptr 0:8)
  0)

(defun fgets (ptr len str)
  (declare (external "fgets" "fgets_unlocked"))
  (if (= len 0) (terminate-string-and-return-null ptr)
    (let ((i 0)
          (n (-1 len))
          (continue true))
      (while (and continue (< i n))
        (let ((c (fgetc str)))
          (if (= c -1)
              (set continue false)
            (memory-write (+ ptr i) (cast char c))
            (set continue (/= c 0xA))
            (incr i))))
      (if (= i 0)
          (terminate-string-and-return-null ptr)
      (memory-write (+ ptr (min n i)) 0:8)
      ptr))))

(defun gets (ptr)
  (declare (external "gets"))
  (let ((str *standard-input*)
        (i 0)
        (continue true))
    (while continue
      (let ((c (fgetc str)))
        (if (= c -1)
            (set continue false)
          (memory-write (+ ptr i) (cast char c))
          (set continue (/= c 0xA))
          (incr i))))
    (memory-write (+ ptr i) 0:8)
    ptr))


(defun getchar ()
  (declare (external "getchar" "getchar_unlocked"))
  (fgetc *standard-input*))

(defmethod primus:machine-kill ()
  (channel-flush *standard-output*)
  (channel-flush *standard-error*))
