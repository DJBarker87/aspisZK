import NBA_PowersCallee
import LPt_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_Nonvacuity
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge LPi_FieldValues

theorem helper_domain : ∃ (y1 : Slice U8) (g : Array NE 29#usize),
    LPt_LPn.Expand.NativeTrace LPt_Nonvacuity.compact.val LPt_Nonvacuity.initial.val 29 y1.val ∧
    LPt_External.compact.expand_values LPt_Nonvacuity.compact LPt_Nonvacuity.initial=ok (.Ok (),y1) ∧
    LPq_SelectedDomain.ByteDomain y1 ∧
    FIo_Native.weights.powers 29#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ONE=ok g ∧
    NBA_Installed.actual.powers 29#usize (NBA_ClaimCallee.wide FIo_Native.aspis_core.field.wide_exact.WideExact.ONE)=
      ok (mapArray NBA_ClaimCallee.wide g) ∧ (∀ z∈g.val,canonE z) := by
  obtain ⟨y1,trace,expanded,bytes⟩ := LPt_Nonvacuity.expanded
  obtain ⟨g,native,cohort,canonical⟩ := NBA_PowersCallee.source 29#usize
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE LPq_Powers.one_canonical
  exact ⟨y1,g,trace,expanded,bytes,native,cohort,canonical⟩

#print axioms helper_domain
end AspisR1.NBA_Nonvacuity
end
