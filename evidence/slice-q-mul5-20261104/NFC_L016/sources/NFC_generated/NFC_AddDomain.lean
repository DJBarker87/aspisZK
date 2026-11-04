import NEV_StageWideFields
import NEV_DotCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_AddDomain
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- Actual final add returns a canonical value on exactly its operand domain. -/
theorem total (left right : NE) (hl : canonE left) (hr : canonE right) :
    ∃ out,FIo_Native.aspis_core.field.wide_exact.WideExact.add left right=ok out ∧ canonE out := by
  obtain ⟨a,ha,ca,_⟩:=LPi_TowerValues.qm_add left.c0 right.c0 hl.1 hr.1
  obtain ⟨b,hb,cb,_⟩:=LPi_TowerValues.qm_add left.c1 right.c1 hl.2 hr.2
  refine ⟨⟨a,b⟩,?_,ca,cb⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]

theorem canonical (left right out : NE) (hl : canonE left) (hr : canonE right)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.add left right=ok out) : canonE out := by
  obtain ⟨value,call,canonical⟩:=total left right hl hr
  have same : value=out := Result.ok.inj (call.symm.trans run)
  exact same ▸ canonical
#print axioms total
#print axioms canonical
end AspisR1.NFC_AddDomain
end
