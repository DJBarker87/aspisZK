import F3S_FinishWitness
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_FinishUnique
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
 theorem unique {W : Type} (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x y : F3S_FinishWitness.Primitives ops v p a) : x=y := by
  cases x with
  | mk xa0 xa1 xr0 xr1 xw xas xp xd xh0 xh1 xhw xhas xhp xhd =>
    cases y with
    | mk ya0 ya1 yr0 yr1 yw yas yp yd yh0 yh1 yhw yhas yhp yhd =>
      have e0 : xa0=ya0 := Result.ok.inj (xh0.symm.trans yh0)
      have e1 : xa1=ya1 := Result.ok.inj (xh1.symm.trans yh1)
      subst ya0
      subst ya1
      have er0 := F3S_RoundUnique.record ops v.round0 xa0 p.claim xr0 yr0
      subst yr0
      have er1 := F3S_RoundUnique.record ops v.round1 xa1 xr0.value xr1 yr1
      subst yr1
      have ew := core.result.Result.Ok.inj (Result.ok.inj (xhw.symm.trans yhw))
      subst yw
      have eas := Result.ok.inj (xhas.symm.trans yhas)
      subst yas
      have ep := core.result.Result.Ok.inj (Result.ok.inj (xhp.symm.trans yhp))
      subst yp
      have ed := core.result.Result.Ok.inj (Result.ok.inj (xhd.symm.trans yhd))
      subst yd
      rfl
#print axioms unique
end AspisR1.F3S_FinishUnique
end
