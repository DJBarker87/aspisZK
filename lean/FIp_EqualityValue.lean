import FIp_Equality
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_EqualityValue
open Aeneas Aeneas.Std Result
open FIp_Equality (E)
attribute [local instance] Classical.propDecidable

theorem injective : Function.Injective FIo_Install.toE := by
  intro x y h
  exact (FIo_Install.from_to x).symm.trans ((congrArg FIo_Install.fromE h).trans (FIo_Install.from_to y))

theorem eq_true (x y : E) (run : FIp_Equality.eq x y=ok true) : x=y := by
  unfold FIp_Equality.eq at run
  rw [FIp_Equality.qm,FIp_Equality.qm] at run
  simp only [bind_tc_ok] at run
  split at run
  · rename_i h0
    have h0 : (FIo_Install.toE x).c0=(FIo_Install.toE y).c0 := by simpa using h0
    have h1 : (FIo_Install.toE x).c1=(FIo_Install.toE y).c1 := by simpa using Result.ok.inj run
    apply injective
    cases hx : FIo_Install.toE x
    cases hy : FIo_Install.toE y
    simp_all only [FIo_Native.aspis_core.field.wide_exact.WideExact.mk.injEq]
  · cases run

theorem ne_false (x y : E)
    (run : core.cmp.PartialEq.ne.trait_default FIp_Equality.dictionary x y=ok false) : x=y := by
  unfold core.cmp.PartialEq.ne.trait_default at run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases b with
  | true => exact eq_true x y hb
  | false => cases run

#print axioms injective
#print axioms eq_true
#print axioms ne_false
end AspisR1.FIp_EqualityValue
end
