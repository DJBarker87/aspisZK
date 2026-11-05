import NHU_Preweighted
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHU_PreweightedFrames
open Aeneas Aeneas.Std Result
open FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
/-- Exact decoded frame for every output outside the updated group interval.
Totality comes from the proved emitted packet, not a native success assumption. -/
theorem result {N : Usize} (packed : Array NQ 24#usize) (start : Usize) (a : Array NQ N)
 (positive : 0<N.val) (interval : start.val+N.val≤96)
 (hp : canonical packed) (ha : canonical a) :
 ∃ out,pool_v1.pair_forest_semantic_terminal.add_preweighted packed start a=ok out ∧
 canonical out ∧ ∀ j : Fin (24#usize).val,
 (j.val<start.val/4 ∨ (start.val+N.val-1)/4<j.val)→decoded out j=decoded packed j := by
 obtain ⟨out,call,canon,value⟩:=NHU_Preweighted.result packed start a positive interval hp ha
 refine ⟨out,call,canon,?_⟩
 intro j outside
 rw [value j]
 have zero:=FIx_PreweightedPointwise.outside a start.val j.val outside
 have same:=FIx_SelectedMeaning.increment a (decoded a) rfl start.val j.val
 rw [←same,zero,add_zero]
#print axioms result
end AspisR1.NHU_PreweightedFrames
end
