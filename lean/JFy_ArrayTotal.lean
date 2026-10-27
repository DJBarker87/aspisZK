import JFy_FieldTotal
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_ArrayTotal
open Aeneas Aeneas.Std Result WP
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)

theorem read {N : Usize} (a : Array NQ N) (i : Usize) (bound : i.val<N.val)
    (hc : FIw_ArrayValue.canonical a) : ∃ q,Array.index_usize a i=ok q ∧ Canon q := by
  have spec : Array.index_usize a i ⦃ _ => True ⦄ := by step* <;> scalar_tac
  obtain ⟨q,call,_⟩ := WP.spec_imp_exists spec
  exact ⟨q,call,FIv_NativeArray.canonical a i q hc call⟩
#print axioms read

theorem update {N : Usize} (a : Array NQ N) (i : Usize) (q : NQ)
    (bound : i.val<N.val) (ha : FIw_ArrayValue.canonical a) (hq : Canon q) :
    ∃ b,Array.update a i q=ok b ∧ FIw_ArrayValue.canonical b := by
  have spec : Array.update a i q ⦃ _ => True ⦄ := by step* <;> scalar_tac
  obtain ⟨b,call,_⟩ := WP.spec_imp_exists spec
  exact ⟨b,call,(FIw_ArrayValue.update a b i q bound ha hq call).1⟩
#print axioms update
end AspisR1.JFy_ArrayTotal
end
