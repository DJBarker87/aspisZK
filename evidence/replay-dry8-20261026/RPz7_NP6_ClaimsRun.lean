import RPz7_NP6_ClaimsMain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ClaimsRun
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent NP6_StdModel

def Content (reservation : Reservation) (pre : ClaimsUnrolledFinish.MainPrefix)
    (out : ClaimsUnrolledFinish.MainClaims) : Prop :=
    reservation = .Ok () ∧ ∃ vr row0 row1 row2,
      (ClaimsUnrolledFinish.external (calls reservation)).validated
        (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8 = ok (.Ok vr) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 0#usize = ok (.Ok row0) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 29#usize = ok (.Ok row1) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 58#usize = ok (.Ok row2) ∧
      out.val = [ClaimsUnrolledFinish.toMainArray row0,
        ClaimsUnrolledFinish.toMainArray row1,ClaimsUnrolledFinish.toMainArray row2]

theorem on_success (reservation : Reservation) (pre : ClaimsUnrolledFinish.MainPrefix)
    (out : ClaimsUnrolledFinish.MainClaims)
    (accepted : ClaimsUnrolledFinish.reference (calls reservation) pre = ok (.Ok out)) :
    Content reservation pre out := NP6_ClaimsMain.main_success reservation pre out accepted

#print axioms on_success
end AspisR1.NP6_ClaimsRun
end
