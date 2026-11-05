import NHG_COMBINED_IMPORT
import NDO_JFy_Preweighted
import RPv_FIx_PreweightedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHU_Preweighted
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
/-- Total emitted packet; no successful-call premise is imported. -/
theorem result {N : Usize} (packed : Array NQ 24#usize) (start : Usize) (a : Array NQ N)
 (positive : 0<N.val) (interval : start.val+N.val≤96)
 (hp : canonical packed) (ha : canonical a) :
 ∃ out,pool_v1.pair_forest_semantic_terminal.add_preweighted packed start a=ok out ∧
 canonical out ∧ ∀ j : Fin (24#usize).val,
 decoded out j=decoded packed j+FIx_SelectedMeaning.contribution (decoded a) start.val j.val := by
 obtain ⟨out,call,canon⟩:=WP.spec_imp_exists (JFy_Preweighted.source packed start a positive interval hp ha)
 exact ⟨out,call,FIx_PreweightedMeaning.value packed out start a (decoded a) rfl positive interval hp ha call⟩
#print axioms result
end AspisR1.NHU_Preweighted
end
