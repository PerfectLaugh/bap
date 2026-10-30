import BapTests.Support

namespace Bap.Tests.Jni

open Bap
open Bap.Emu.Jni

private def call (index : Nat) (args : List Nat := []) : Call :=
  ⟨index, (args ++ List.replicate (8 - min args.length 8) 0).toArray⟩

def run : IO Unit := do
  let fallbacks ← IO.mkRef 0
  let model ← create
    (fun address => pure (match address with
      | 0x100 => "example/Class"
      | 0x110 => "perform"
      | 0x120 => "()V"
      | 0x130 => "value"
      | 0x140 => "J"
      | 0x150 => "contents"
      | _ => ""))
    (fun _ => pure 0x52040000)
    (fun _ => pure 0x52050000)
    (fun _ _ => do
      fallbacks.modify (· + 1)
      pure (.value 0x77))
  let localHandle ← intern model 0x9001
  let globalHandle ← dispatch model (call 21 [0, localHandle])
  assertEqual "JNI local and global handles preserve identity" 1
    (← dispatch model (call 24 [0, localHandle, globalHandle]))
  let classFirst ← dispatch model (call 6 [0, 0x100])
  let classSecond ← dispatch model (call 6 [0, 0x100])
  assertEqual "JNI class handles are stable" classFirst classSecond
  let methodFirst ← dispatch model (call 33 [0, classFirst, 0x110, 0x120])
  let methodSecond ← dispatch model (call 33 [0, classFirst, 0x110, 0x120])
  assertEqual "JNI method IDs are stable" methodFirst methodSecond
  assertEqual "JNI dynamic method name" (some "perform") (← dynamicName model methodFirst)
  assertEqual "JNI known operations do not invoke fallback" 0 (← fallbacks.get)
  assertEqual "JNI dynamic method uses fallback once" 0x77
    (← dispatch model (call 34 [0, localHandle, methodFirst]))
  assertEqual "JNI dynamic method fallback count" 1 (← fallbacks.get)
  let field ← dispatch model (call 94 [0, classFirst, 0x130, 0x140])
  assertEqual "JNI dynamic field name" (some "value") (← dynamicName model field)
  assertEqual "JNI field fallback count remains lazy" 1 (← fallbacks.get)
  let string ← dispatch model (call 167 [0, 0x150])
  assertEqual "JNI string length" 8 (← dispatch model (call 168 [0, string]))
  let charsFirst ← dispatch model (call 169 [0, string])
  let charsSecond ← dispatch model (call 169 [0, string])
  assertEqual "JNI string buffers are stable" charsFirst charsSecond
  assertEqual "JNI string operations avoid fallback" 1 (← fallbacks.get)
  let bytes ← dispatch model (call 176 [0, 3])
  assertEqual "JNI byte-array length" 3 (← dispatch model (call 171 [0, bytes]))
  let bytesFirst ← dispatch model (call 184 [0, bytes])
  let bytesSecond ← dispatch model (call 184 [0, bytes])
  assertEqual "JNI byte-array buffer is allocated" 0x52050000 bytesFirst
  assertEqual "JNI byte-array buffer is stable" bytesFirst bytesSecond
  let objects ← dispatch model (call 172 [0, 1, classFirst, string])
  assertEqual "JNI object-array initial element" string (← dispatch model (call 173 [0, objects, 0]))
  let _ ← dispatch model (call 174 [0, objects, 0, localHandle])
  assertEqual "JNI object-array updated element" localHandle (← dispatch model (call 173 [0, objects, 0]))
  assertEqual "JNI array operations avoid fallback" 1 (← fallbacks.get)
  let _ ← dispatch model (call 17)
  assertEqual "JNI ExceptionCheck is initially clear" 0 (← dispatch model (call 228))
  let _ ← dispatch model (call 13 [0, string])
  assertEqual "JNI ExceptionCheck observes Throw" 1 (← dispatch model (call 228))
  assertEqual "JNI ExceptionOccurred returns the thrown object" string (← dispatch model (call 15))
  let _ ← dispatch model (call 17)
  assertEqual "JNI ExceptionClear resets ExceptionCheck" 0 (← dispatch model (call 228))
  assertEqual "JNI unknown operation uses fallback" 0x77 (← dispatch model (call 229))
  assertEqual "JNI unknown operation fallback count" 2 (← fallbacks.get)

end Bap.Tests.Jni
