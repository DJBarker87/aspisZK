import Aeneas
import PRVEq_Tx2Deployed_n1
import PRVEq_Resume_q13
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Probe3
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1
#print OraclePortStdAllocation.filled
#print OraclePortCkptAbi2Unwrap.unwrapWithPanic
#print AspisR1Stage2.verifier.Reader.rawWithUnwrap
#check @CheckpointBytes3Namespaces.fromK
#check @OraclePortCkptAbi2Extracted.decode_k_spec
#check @NIL_FreshOps.any
#check @NIL_FreshOps.mapError
#print VTop_Stages.PRVFresh_VTop_l1.core.option.Option.ok_or
#print AspisR1Stage2.verifier.Reader
#print VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.k
example : ∀ n r, VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.raw n r = CheckpointBytes3Reader.raw n r := by
  intro n r; rfl
end PCVQ_Probe3
