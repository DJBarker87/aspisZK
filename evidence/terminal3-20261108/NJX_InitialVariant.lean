import NHG_ExtraLeaves
import NJB_StubLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_InitialVariant
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
abbrev Variant := FIq_Native.pool_v1.pair_forest_semantic_terminal.CompiledVariant
/-- Canonical full4Result supplement for CLOSED initial_variant_selectors,
needed by SAME caller260; no new row or native credit for this callee. -/
theorem source (v : Variant) (a b c : NQ) (ha : Canon a) (hb : Canon b) (hc : Canon c) :
 ∃ (t f eight two : NQ),FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors v a b c=ok (t,f,eight,two) ∧
 Canon t ∧ Canon f ∧ Canon eight ∧ Canon two := by
 obtain ⟨ab,cab,hab,_⟩ := NJB_StubLaws.qm_add a b ha hb
 rw [NHG_ExtraLeaves.initial_source]
 cases v with
 | PrivateTransfer=>exact ⟨a,FIq_Native.field.QM31.ZERO,ab,c,by simp only [NHG_ExtraLeaves.initialBody,cab,bind_tc_ok],ha,FIv_NativeValue.zero.1,hab,hc⟩
 | Withdrawal=>
   obtain ⟨abc,cabc,habc,_⟩ := NJB_StubLaws.qm_add ab c hab hc
   exact ⟨FIq_Native.field.QM31.ZERO,abc,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,
    by simp only [NHG_ExtraLeaves.initialBody,cab,cabc,bind_tc_ok],FIv_NativeValue.zero.1,habc,FIv_NativeValue.zero.1,FIv_NativeValue.zero.1⟩
#print source
#print axioms source
end AspisR1.NJX_InitialVariant
end
