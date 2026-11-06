import NJR_AcceptedFinishDomain
set_option autoImplicit false
noncomputable section
namespace NJU_CurrentWindows
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Predicate on the actual current View; no proof history or digest premise. -/
def Holds (v : verifier.View) : Prop :=
 NIG_FinishInput.Windows v.round0 7 ∧ NIG_FinishInput.Windows v.round1 7 ∧
 NIG_FinishInput.Windows v.final_message 64

theorem split (v : verifier.View) : Holds v ∨ ¬ Holds v := Classical.em _

/-- An off-domain source finish cannot accept. This is only rejection, not
complete native Result/effect correspondence required by (aw)(3)(b). -/
theorem rejects (r : NP6_StdModel.Reservation) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) (s2 : p.variant=.S2)
 (width : a.weights.val.length=64)
 (r0size : v.round0.val.length=224) (r1size : v.round1.val.length=224)
 (finalSize : v.final_message.val.length=2048) (bad : ¬ Holds v) :
 Port4D_FinishInstall.finish (IDa_Deployed.finish r) v p a none ≠ ok (.Ok ()) := by
 intro accepted
 exact bad (NJR_WindowsFromFinish.source r v p a s2 width r0size r1size finalSize accepted)

#print axioms split
#print axioms rejects
end NJU_CurrentWindows
