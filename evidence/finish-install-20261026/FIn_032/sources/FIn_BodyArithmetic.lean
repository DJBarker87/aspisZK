import FIn_ExtractInstall
import FIn_Round
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_BodyArithmetic
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

theorem value (bytes : Slice U8) (x out : E) (f : Fin 7 → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f=MultiproofConeCanonical.bytesOf bytes.val)
    (run : FIn_ExtractInstall.polynomial bytes x=ok out) :
    CheckpointBytes5Output.ofE out=(OpeningPolynomialView.polynomial f).eval (CheckpointBytes5Output.ofE x) := by
  rw [FIn_ExtractInstall.same] at run
  exact FIn_Polynomial.value bytes x out f encoded run

#print axioms value
end AspisR1.FIn_BodyArithmetic
end
