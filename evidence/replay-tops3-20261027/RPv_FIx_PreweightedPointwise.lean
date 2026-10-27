import RPv_FIx_Preweighted
import RPv_FIx_PreweightedModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedPointwise
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)

theorem outside {N : Usize} (a : Array NQ N) (start group : Nat)
    (bound : group<start/4 ∨ (start+N.val-1)/4<group) :
    FIx_PreweightedGroup.increment a start group=0 := by
  have zero : (fun i : Fin (4#usize).val=>FIx_PreweightedSelect.selected a start group i.val)=fun _=>0 := by
    funext i
    have hi : i.val<4 := i.isLt
    unfold FIx_PreweightedSelect.selected
    rw [if_neg]
    intro inside
    rcases bound with h | h <;> omega
  unfold FIx_PreweightedGroup.increment
  rw [zero]
  simp only [FIx_PreweightedPack.pack,mul_zero,add_zero]

theorem value {N : Usize} (packed out : Array NQ 24#usize) (start : Usize) (a : Array NQ N)
    (positive : 0<N.val) (interval : start.val+N.val≤96)
    (hp : canonical packed) (ha : canonical a)
    (success : pool_v1.pair_forest_semantic_terminal.add_preweighted packed start a=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+FIx_PreweightedGroup.increment a start.val j.val := by
  have source := FIx_Preweighted.value packed out start a positive interval hp ha success
  refine ⟨source.1,?_⟩
  intro j
  rw [source.2,FIx_PreweightedModel.value]
  by_cases inside : start.val/4≤j.val ∧ j.val<start.val/4+FIx_Preweighted.count start.val N.val
  · rw [if_pos inside]
  · rw [if_neg inside]
    have ascending : start.val/4≤(start.val+N.val-1)/4 := by omega
    have out : j.val<start.val/4 ∨ (start.val+N.val-1)/4<j.val := by
      unfold FIx_Preweighted.count at inside
      omega
    rw [outside a start.val j.val out]
#print axioms outside
#print axioms value
end AspisR1.FIx_PreweightedPointwise
end
