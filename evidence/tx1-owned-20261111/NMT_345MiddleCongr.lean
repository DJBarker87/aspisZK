import NMT_345MiddleFold
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Five source calls with their original parent; no child is evaluated. -/
theorem middle_congr {W : Type} (c : Calls) (s : Decoded W)
 (f g : ProofData W → Result Ret) (same : ∀ d,f d = g d) :
 middleFold c s f = middleFold c s g := by
 unfold middleFold
 apply AspisR1.NMT_CallTree.result_congr
 intro validation
 apply try_congr
 intro _
 apply AspisR1.NMT_CallTree.result_congr
 intro common
 apply AspisR1.NMT_CallTree.result_congr
 intro encoded
 apply try_congr
 intro candidate
 apply try_congr
 intro proof
 exact same _
#print axioms middle_congr
end NMT_345
