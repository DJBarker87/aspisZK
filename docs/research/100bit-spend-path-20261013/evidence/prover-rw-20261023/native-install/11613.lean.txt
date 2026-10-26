import R1Z.ProverRwDictionaryScalar
import R1Z.ProverCommitWideOps48
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryCorrectWAdd
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48
variable [ExternalTypes]
abbrev input (x : Raw) : ProverRwDictionaryTower.W :=
  ProverRwDictionaryTower.fromW (source x)

/-- The source arithmetic is installed; only the actual canonical input
invariant remains. No source success or operation/model equality is assumed. -/
theorem correct (ops : ExternalFuns) (x y : Raw) (hx : canonical x) (hy : canonical y) :
    ∃ z : Raw,
      (ProverRwDictionaryScalar.selected ops).op46 (input x) (input y) = .ok (input z) ∧
      canonical z ∧ value z = value x + value y := by
  obtain ⟨z,hz,hc,hd⟩ := ProverCommitWideOps48.add_exact x y hx hy
  refine ⟨z,?_,hc,hd⟩
  have entry : (ProverRwDictionaryScalar.selected ops).op46 = ProverRwDictionaryTower.wAdd := rfl
  rw [entry]
  unfold ProverRwDictionaryTower.wAdd input
  rw [ProverRwDictionaryTower.native_w_roundtrip,ProverRwDictionaryTower.native_w_roundtrip,hz]
  rfl

#print axioms correct
end R1Z.ProverRwDictionaryCorrectWAdd
