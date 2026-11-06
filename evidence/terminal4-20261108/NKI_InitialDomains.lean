import NKI_InitialTraceFactor
import NJB_PreparedLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialDomains
open Aeneas Aeneas.Std Result
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
theorem source (p : Public) (o : Openings) (s : Selectors) (l : Locals)
 (calls : NKI_InitialInvocation.Clauses p o s l) (hc : NKI_InitialTrace.Canonical l) :
 NJB_PreparedLaws.Domain l.full l.full_initial_selector ∧ NJB_PreparedLaws.Domain l.full_or_rate l.q12 := by
 have call_full : FIq_Native.field.PreparedQm31Multiplier.new l.full_initial_selector=ok l.full := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have canon_full : FIv_NativeValue.Canon l.full_initial_selector := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 obtain ⟨v_full,cv_full,hv_full⟩ := NJB_PreparedLaws.new_result l.full_initial_selector canon_full
 have eq_full : v_full=l.full := Result.ok.inj (cv_full.symm.trans call_full)
 rw [eq_full] at hv_full
 have call_full_or_rate : FIq_Native.field.PreparedQm31Multiplier.new l.q12=ok l.full_or_rate := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have canon_full_or_rate : FIv_NativeValue.Canon l.q12 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 obtain ⟨v_full_or_rate,cv_full_or_rate,hv_full_or_rate⟩ := NJB_PreparedLaws.new_result l.q12 canon_full_or_rate
 have eq_full_or_rate : v_full_or_rate=l.full_or_rate := Result.ok.inj (cv_full_or_rate.symm.trans call_full_or_rate)
 rw [eq_full_or_rate] at hv_full_or_rate
 exact ⟨hv_full,hv_full_or_rate⟩
#print axioms source
end AspisR1.NKI_InitialDomains
end
