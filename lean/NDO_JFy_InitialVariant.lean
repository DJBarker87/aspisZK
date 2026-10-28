import RPv_JFy_Steps
import RPu_FIq_Native10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_InitialVariant
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_semantic_terminal

theorem source (v : CompiledVariant) (a b c : field.QM31) (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    ∃ out,initial_variant_selectors v a b c=ok out ∧ Canon out.1 ∧ Canon out.2.1 ∧ Canon out.2.2.1 ∧ Canon out.2.2.2 := by
  have zero := FIv_NativeValue.zero.1
  cases v with
  | PrivateTransfer =>
    obtain ⟨sum,call,hcSum,_⟩ := FIv_PreparedTotal.add a b ha hb
    have run : initial_variant_selectors .PrivateTransfer a b c=ok (a,field.QM31.ZERO,sum,c) := by
      unfold initial_variant_selectors
      rw [call,bind_tc_ok]
    exact ⟨_,run,ha,zero,hcSum,hc⟩
  | Withdrawal =>
    obtain ⟨sum,call,hcSum,_⟩ := FIv_PreparedTotal.add a b ha hb
    obtain ⟨sum1,call1,hcSum1,_⟩ := FIv_PreparedTotal.add sum c hcSum hc
    have run : initial_variant_selectors .Withdrawal a b c=ok (field.QM31.ZERO,sum1,field.QM31.ZERO,field.QM31.ZERO) := by
      unfold initial_variant_selectors
      change (do let sum ← field.QM31.add a b
                 let sum1 ← field.QM31.add sum c
                 ok (field.QM31.ZERO,sum1,field.QM31.ZERO,field.QM31.ZERO))=ok _
      rw [call,bind_tc_ok,call1,bind_tc_ok]
    exact ⟨_,run,zero,hcSum1,zero,zero⟩
#print axioms source
@[step] theorem spec (v : CompiledVariant) (a b c : field.QM31) (ha : Canon a) (hb : Canon b) (hc : Canon c) :
    initial_variant_selectors v a b c ⦃ out => Canon out.1 ∧ Canon out.2.1 ∧ Canon out.2.2.1 ∧ Canon out.2.2.2 ⦄ := by
  apply exists_imp_spec
  exact source v a b c ha hb hc
#print axioms spec
end AspisR1.JFy_InitialVariant
end
