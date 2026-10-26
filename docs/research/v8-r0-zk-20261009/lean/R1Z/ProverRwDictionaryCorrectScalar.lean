import R1Z.ProverRwDictionaryScalar
import R1Z.ProverCommitWideScalar48
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryCorrectScalar
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48
variable [ExternalTypes]
abbrev input (x : Raw) : ProverRwDictionaryTower.W := ProverRwDictionaryTower.fromW (source x)

/-- All raw source coordinates and raw rhs words are admitted. The native
callee normalizes the rhs; no canonical-input or success premise is supplied. -/
theorem total (ops : ExternalFuns) (x : Raw) (y : U32) :
    (ProverRwDictionaryScalar.selected ops).op52 (input x) y =
      .ok (input (ProverCommitWideScalar48.product x y)) := by
  have h := ProverCommitWideScalar48.source_exact x y
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromW
    (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_m31
      (ProverRwDictionaryTower.toW (ProverRwDictionaryTower.fromW _)) y) = _
  rw [ProverRwDictionaryTower.native_w_roundtrip,h.1]
  rfl

#print axioms total
end R1Z.ProverRwDictionaryCorrectScalar
