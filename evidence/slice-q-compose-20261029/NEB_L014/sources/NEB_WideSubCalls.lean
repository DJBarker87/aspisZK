import NBG_CheckedSub
set_option autoImplicit false
namespace NEB_WideSubCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- FIo has no WideExact.sub declaration. Use the existing emitted checked
carrier, explicitly rather than inventing a FIo function with that name. -/
theorem source (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ a b,
      AspisR1CurrentWide.field.QM31.sub
        (NBG_GetterPorts.qm x.c0) (NBG_GetterPorts.qm y.c0)=ok (NBG_GetterPorts.qm a) ∧ canonQ a ∧
      AspisR1CurrentWide.field.QM31.sub
        (NBG_GetterPorts.qm x.c1) (NBG_GetterPorts.qm y.c1)=ok (NBG_GetterPorts.qm b) ∧ canonQ b ∧
      AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y)=ok (NBG_GetterPorts.wide ⟨a,b⟩) := by
  obtain ⟨a,ha,ca,_⟩ := NBG_CheckedSub.qm_result x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := NBG_CheckedSub.qm_result x.c1 y.c1 hx.2 hy.2
  exact ⟨a,b,ha,ca,hb,cb,by
    simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub,NBG_GetterPorts.wide,ha,hb,bind_tc_ok]⟩

#print axioms source
end NEB_WideSubCalls
