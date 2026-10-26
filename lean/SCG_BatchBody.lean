import GExq_BatchSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_BatchBody
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)

/-- Cross-carrier phantom erasure, before touching the recursive batch loop. -/
theorem dictionary (base : Port3_NativeBatchBody.Ops) {H K : Type}
    (D : aspis_core.digest.Digest32 H) (E : aspis_core.digest.Digest32 K) (h : H) (k : K)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchStep.body base D proof root tree h lo n slot keys idx val d pos =
      Port9OR_BatchStep.body base E proof root tree k lo n slot keys idx val d pos := by
  rfl

#print axioms dictionary
end AspisR1.SCG_BatchBody
end
