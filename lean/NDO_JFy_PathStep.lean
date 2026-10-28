import RPv_JFy_Steps
import RPv_FIx_PathStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PathStep
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)

@[step] theorem source (lane : Usize) (selector bit : field.QM31) (a b : Array field.QM31 16#usize)
    (path : Array field.QM31 17#usize) (hl : lane.val<8) (hs : Canon selector) (hb : Canon bit)
    (ha : canonical a) (hbb : canonical b) (hp : canonical path) :
    FIx_PathStep.run lane selector a b bit path ⦃ out => canonical out ⦄ := by
  have one := FIv_NativeValue.one.1
  unfold FIx_PathStep.run poseidon2.RATE poseidon2.DIGEST_ELEMS
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JFy_PathStep
end
