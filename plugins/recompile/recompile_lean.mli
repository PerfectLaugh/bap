val split_proof : Recompile_llvm_ir.split_witness -> (string, string) result
val validate_split : Recompile_llvm_ir.split_witness -> (unit, string) result
val thread_proof : Recompile_llvm_ir.thread_witness -> (string, string) result
val validate_thread : Recompile_llvm_ir.thread_witness -> (unit, string) result
