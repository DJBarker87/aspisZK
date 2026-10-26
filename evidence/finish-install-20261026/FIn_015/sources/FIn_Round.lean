import FIn_Install
import Port4D_Pairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Round
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

/-- A byte encoding identity, rather than an arithmetic-law hypothesis. -/
theorem laws {W : Type} (seed : FinishOps W) (bytes : Slice U8)
    (f : Fin 7 → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f = MultiproofConeCanonical.bytesOf bytes.val) :
    Port4D_Pairing.RoundLaws (FIn_Install.finishOps seed) CheckpointBytes5Output.ofE
      bytes (OpeningPolynomialView.polynomial f) := by
  refine ⟨?_,?_,?_⟩
  · intro c0 c4 lhs h0 h4 ha
    have v0 := FIn_Polynomial.encoded_field bytes f encoded 0#usize c0 (by decide) h0
    have v4 := FIn_Polynomial.encoded_field bytes f encoded 4#usize c4 (by decide) h4
    have sum := FIn_Primitives.add_value c0 c4 lhs ha
    rw [v0,v4] at sum
    exact sum.trans (OpeningPolynomialView.firstPolynomial_boundary f).symm
  · intro m claim rhs hq hm
    exact SAG_StageScale.quarter seed m claim rhs hq hm
  · intro alpha value run
    exact FIn_Polynomial.value bytes alpha value f encoded run

#print axioms laws
end AspisR1.FIn_Round
end
