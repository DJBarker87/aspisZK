import Port6CK_Semantic
import Port6CK_Weights
import Port5Q2_ReaderValidate
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Ops
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Semantic (Unwrap current)
/-- Current helper implementations at the retained parent's exact leaves.
The other leaves retain the existing Std/allocator/P6 interpretation. -/
def ops (reserved : Bool) (unwrap : Unwrap) : ResumeOps :=
  { CheckpointBytes4Ops.ops reserved with
    raw := fun N => Port5Q2_ReaderRaw.raw N (unwrap N)
    readK := current unwrap
    readE := Port5Q2_ReaderScalar.readE (fun N => Port5Q2_ReaderRaw.raw N (unwrap N))
      Port5Q2_ReaderScalar.decodeE
    readSemanticAlpha := Port5Q2_ReaderSemantic.semantic (current unwrap)
    validate := Port5Q2_ReaderValidate.validate
    readWeights := Port5Q2_ReaderWeights.weights (current unwrap) }

end AspisR1.Port6CK_Ops
end
