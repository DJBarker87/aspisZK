import Port3_FlushInstall
set_option autoImplicit false
namespace AspisR1.SAG_FlushLength
open Aeneas Aeneas.Std Result
open VTop_Stages

theorem length (b : verifier.BatchedWeights) (old out : Slice aspis_core.field.QM31)
    (oldSize : old.val.length = 64) (rawSize : b.raw.val.length = 64)
    (success : Port3_FlushInstall.flush b old = ok out) : out.val.length = 64 := by
  have bounded : old.val.length ≤ b.raw.val.length := by rw [oldSize,rawSize]
  exact (Port3_FlushInstall.accepted_contents b old out bounded success).2.trans oldSize

#print axioms length
end AspisR1.SAG_FlushLength
