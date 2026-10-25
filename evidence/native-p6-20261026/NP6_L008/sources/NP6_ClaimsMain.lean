import NP6_ClaimsSuccess

set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ClaimsMain
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent NP6_StdModel

/-- Recover the SAME successful parent carrier from the selected main-carrier
reference. Error/fail/div branches cannot supply success. -/
theorem main_success (reservation : Reservation)
    (pre : ClaimsUnrolledFinish.MainPrefix) (out : ClaimsUnrolledFinish.MainClaims)
    (accepted : ClaimsUnrolledFinish.reference (calls reservation) pre = ok (.Ok out)) :
    reservation = .Ok () ∧ ∃ vr row0 row1 row2,
      (ClaimsUnrolledFinish.external (calls reservation)).validated
        (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8 = ok (.Ok vr) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 0#usize = ok (.Ok row0) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 29#usize = ok (.Ok row1) ∧
      (ClaimsUnrolledFinish.external (calls reservation)).decode 29#usize vr 58#usize = ok (.Ok row2) ∧
      out.val = [ClaimsUnrolledFinish.toMainArray row0,
        ClaimsUnrolledFinish.toMainArray row1,ClaimsUnrolledFinish.toMainArray row2] := by
  cases hp : claimsReference (ClaimsUnrolledFinish.external (calls reservation))
      (ClaimsUnrolledFinish.fromMainPrefix pre) with
  | fail e => simp [ClaimsUnrolledFinish.reference,ClaimsUnrolledFinish.toMainStatus,hp] at accepted
  | div => simp [ClaimsUnrolledFinish.reference,ClaimsUnrolledFinish.toMainStatus,hp] at accepted
  | ok r =>
    cases r with
    | Err e => simp [ClaimsUnrolledFinish.reference,ClaimsUnrolledFinish.toMainStatus,hp] at accepted
    | Ok parent =>
      obtain ⟨allocated,vr,row0,row1,row2,hv,h0,h1,h2,contents⟩ :=
        NP6_ClaimsSuccess.reference_success reservation _ parent hp
      have hm : (⟨parent.val.map ClaimsUnrolledFinish.toMainArray,by simpa using parent.property⟩ :
          ClaimsUnrolledFinish.MainClaims) = out := by
        simpa [ClaimsUnrolledFinish.reference,ClaimsUnrolledFinish.toMainStatus,hp] using accepted
      have mapped := congrArg (List.map ClaimsUnrolledFinish.toMainArray) contents
      have hvout := congrArg Subtype.val hm
      exact ⟨allocated,vr,row0,row1,row2,hv,h0,h1,h2,hvout.symm.trans (by simpa using mapped)⟩

#print axioms main_success
end AspisR1.NP6_ClaimsMain
end
