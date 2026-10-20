;; the functions of msvcrt and KERNEL32, that the startup code of mingw
;; calls, as the programs of PE import them, see api/c/windows.h; the int
;; of Windows is int32_t, on x86 and x86-64

(require stdlib)
(require string)
(require types)

(in-package posix)

;; KERNEL32

(defun GetSystemTimeAsFileTime (time)
  (declare (external "GetSystemTimeAsFileTime"))
  (memset time 0 8))

(defun GetCurrentProcessId ()
  (declare (external "GetCurrentProcessId" "GetCurrentThreadId"))
  1)

(defun GetCurrentProcess ()
  "the pseudo handle of the current process"
  (declare (external "GetCurrentProcess"))
  -1)

(defun GetTickCount ()
  (declare (external "GetTickCount"))
  0)

(defun QueryPerformanceCounter (count)
  (declare (external "QueryPerformanceCounter"))
  (memset count 0 8)
  1)

(defun GetLastError ()
  (declare (external "GetLastError"))
  0)

(defun GetStartupInfoA (info)
  "zeroes STARTUPINFOA, whose size is its first field"
  (declare (external "GetStartupInfoA"))
  (memset info 0 (+ 32 (* 9 (sizeof ptr_t))))
  (write-word int32_t info (+ 32 (* 9 (sizeof ptr_t)))))

(defun Sleep (milliseconds)
  (declare (external "Sleep"))
  0)

(defun InitializeCriticalSection (section)
  (declare (external "InitializeCriticalSection"
                     "DeleteCriticalSection"
                     "EnterCriticalSection"
                     "LeaveCriticalSection"))
  0)

(defun TlsGetValue (index)
  (declare (external "TlsGetValue"))
  0)

(defun SetUnhandledExceptionFilter (filter)
  "returns the previous filter, which is none"
  (declare (external "SetUnhandledExceptionFilter"))
  0)

(defun UnhandledExceptionFilter (info)
  "EXCEPTION_CONTINUE_SEARCH"
  (declare (external "UnhandledExceptionFilter"))
  0)

(defun ExitProcess (code)
  (declare (external "ExitProcess"))
  (exit-with code))

(defun TerminateProcess (process code)
  (declare (external "TerminateProcess"))
  (exit-with code))

(defun VirtualQuery (addr buffer length)
  "the page of ADDR is committed and executable, as MEMORY_BASIC_INFORMATION
   tells, whose fields after the bases and the protection of the allocation
   are aligned to the pointers, so that the programs, which write it, e.g.,
   the pseudo relocations of mingw, call VirtualProtect, which makes it
   writable"
  (declare (external "VirtualQuery"))
  (let ((page (logand addr (lnot 0xFFF)))
        (ptr (sizeof ptr_t))
        (size (if (= ptr 8) 48 28)))
    (memset buffer 0 size)
    (write-word ptr_t buffer page)
    (write-word ptr_t (+ buffer ptr) page)
    (write-word int32_t (+ buffer (* 2 ptr)) 0x20)
    (let ((rest (+ buffer (* 3 ptr))))
      (write-word ptr_t rest 0x1000)
      (write-word int32_t (+ rest ptr) 0x1000)
      (write-word int32_t (+ rest ptr 4) 0x20)
      (write-word int32_t (+ rest ptr 8) 0x20000))
    size))

(defun windows-protection-to-posix (protect)
  "the bits PROT_READ, PROT_WRITE, and PROT_EXEC of the PAGE_ constant"
  (case (logand protect 0xFF)
    0x01 0
    0x02 1
    0x04 3
    0x08 3
    0x10 4
    0x20 5
    0x40 7
    0x80 7
    7))

(defun VirtualProtect (addr size protect old)
  "the old protection is PAGE_EXECUTE_READ, as VirtualQuery tells"
  (declare (external "VirtualProtect"))
  (memory-protect addr size (windows-protection-to-posix protect))
  (write-word int32_t old 0x20)
  1)

(defun RtlAddFunctionTable (table count base)
  (declare (external "RtlAddFunctionTable"))
  1)

(defun RtlCaptureContext (context)
  (declare (external "RtlCaptureContext"))
  0)

;; msvcrt

(defun __set_app_type (type)
  (declare (external "__set_app_type" "__setusermatherr" "_lock" "_unlock"))
  0)

(defun __lconv_init ()
  (declare (external "__lconv_init" "_cexit"))
  0)

(defun __dllonexit (func begin end)
  (declare (external "__dllonexit"))
  func)

(defun _onexit (func)
  (declare (external "_onexit"))
  func)

(defun _amsg_exit (code)
  (declare (external "_amsg_exit"))
  (exit-with 255))

(defun __C_specific_handler (record frame context dispatch)
  "ExceptionContinueSearch"
  (declare (external "__C_specific_handler"))
  1)

(defun signal (signum handler)
  "the signals are not delivered, SIG_DFL is the previous handler"
  (declare (external "signal"))
  0)

(defun __iob_func ()
  "the streams are the file descriptors, so stdin is the null stream"
  (declare (external "__iob_func"))
  0)

(defun __getmainargs (argc argv envp wildcard info)
  "the arguments and the environment of the main frame, that the loader
   made, which are argc, argv, and envp after the null of argv"
  (declare (external "__getmainargs"))
  (let ((count (read-word ptr_t main-frame))
        (args (ptr+1 ptr_t main-frame)))
    (write-word int32_t argc count)
    (write-word ptr_t argv args)
    (write-word ptr_t envp (ptr+ ptr_t args (+ count 1)))
    0))

(defun _initterm (begin end)
  "calls the functions of the table, which are not null"
  (declare (external "_initterm"))
  (while (< begin end)
    (let ((func (read-word ptr_t begin)))
      (when func (invoke-subroutine func)))
    (set begin (ptr+1 ptr_t begin))))
