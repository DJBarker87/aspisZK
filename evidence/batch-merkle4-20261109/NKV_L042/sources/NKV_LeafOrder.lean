import NKV_LeafBuild
set_option autoImplicit false
noncomputable section
namespace NKV_LeafOrder
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames
open OraclePortFrozenOrder OraclePortSelectedDraft
open NKV_LeafBuild
attribute [local instance] Classical.propDecidable

theorem key_value (q : Fin 22 → Fin 262144) (kind pos : Nat) :
 (MultiproofConeLeafFold.key q kind pos).val=index q kind pos := rfl

theorem key_bound (q : Fin 22 → Fin 262144) (kind pos : Nat) :
 (MultiproofConeLeafFold.key q kind pos).val<262144 := by
 rw [key_value]
 simp only [index]
 have h := (q ⟨pos%22,Nat.mod_lt _ (by decide)⟩).isLt
 split <;> omega

theorem positions_ordered (q : Fin 22 → Fin 262144) (batch kind : Nat) :
 ((sortedPositions q batch kind).map (index q kind)).Pairwise (·≤·) := by
 have sorted:=List.pairwise_mergeSort
   (le:=fun a b : Nat => decide (index q kind a < index q kind b ∨
     index q kind a=index q kind b ∧ a≤b))
   (by intro a b c ab bc;simp only [decide_eq_true_eq] at *;omega)
   (by intro a b;simp only [Bool.or_eq_true,decide_eq_true_eq];omega)
   (batchPositions batch)
 apply List.pairwise_map.mpr
 exact sorted.imp (by intro a b ordered;have h:=of_decide_eq_true ordered;omega)

theorem size (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) :
 (leaves H p q kind (sortedPositions q batch kind)).length≤12 := by
 simpa only [leaves,List.length_map] using MultiproofConeLeafFrozen.sorted_length q batch kind

theorem nonempty (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) :
 leaves H p q kind (sortedPositions q batch kind)≠[] := by
 intro h
 have length:=congrArg List.length h
 simp only [leaves,List.length_map,sortedPositions,List.length_mergeSort,
   batchPositions,List.length_nil] at length
 split at length <;> simp at length

theorem ordered (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch kind : Nat) :
 ((leaves H p q kind (sortedPositions q batch kind)).map (fun x => x.1.val)).Pairwise (·≤·) := by
 simpa only [leaves,List.map_map,Function.comp_def,key_value]
   using positions_ordered q batch kind

theorem canonical (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) :
 ∀ leaf∈leaves H p q kind positions,leaf.1.val<262144 := by
 intro leaf member
 obtain ⟨pos,mem,rfl⟩:=List.mem_map.mp member
 exact key_bound q kind pos

set_option pp.proofs false
#print positions_ordered
#print axioms key_value
#print axioms key_bound
#print axioms positions_ordered
#print axioms size
#print axioms nonempty
#print axioms ordered
#print axioms canonical
end NKV_LeafOrder
end
