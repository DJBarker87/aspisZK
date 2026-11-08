import LIBC_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CheckpointValue
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect
/-- Erase the exact three-query checkpoint execution already returned by the
canonical library, without evaluating any full checkpoint buffer. -/
theorem source (a : LIBC_Checkpoint.Args) (env : RSL.Env) :
 erase (LIBC_Checkpoint.digest env) ()
  (CheckpointBytes5Writer.writer (LIBC_Checkpoint.prepared a) (LIBC_Checkpoint.accumulator a)
   (LIBC_Bytes.raw a.2.2.1) (LIBC_Bytes.raw a.2.2.2)) = .ok (LIBC_Checkpoint.output a env) :=
 run_success _ _ _ _ _ _ (LIBC_Checkpoint.run_model a env)
#print axioms source
end AspisR1.NNV_CheckpointValue
end
