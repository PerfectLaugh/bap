import Bap.Emu.Jni
import Bap.Linux.Machine

/-! `java/io/File` of a JNI model, from the files of a machine. -/

namespace Bap.Linux

/-- What `java/io/File` of a JNI model finds, from the files of a machine's kernel as they are when it asks: whether a path is there,
whether it is a directory, what is in one, and how big a file is. A path that isn't absolute is of `/`. -/
def Machine.jniFiles (machine : Machine) : Bap.Emu.Jni.FileSystem where
  present path := do pure ((← machine.kernel.get).statPath "/" path |>.toOption).isSome
  isDirectory path := do
    pure (match (← machine.kernel.get).statPath "/" path with
      | .ok stat => stat.mode &&& 0o170000 == 0o040000
      | .error _ => false)
  list path := do
    let kernel ← machine.kernel.get
    match kernel.resolve "/" path with
    | .ok (normal, some _) => pure ((kernel.children normal).map (·.1))
    | _ => pure []
  size path := do
    pure (match (← machine.kernel.get).statPath "/" path with
      | .ok stat => stat.size
      | .error _ => 0)

end Bap.Linux
