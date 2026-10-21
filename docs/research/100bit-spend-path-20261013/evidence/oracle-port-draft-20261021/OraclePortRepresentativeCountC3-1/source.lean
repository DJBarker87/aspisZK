import OraclePortSparseLeafCountC3

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRepresentativeCountC3
open OraclePortSelectedDraft OraclePortBatchDraft
open OracleDecisionMultiTree OracleDecisionMultiBuild
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

/-- First-occurrence representative of a selected key. -/
theorem representative (q : Fin 22 → Fin 262144) (batch kind i : Nat)
    (hi : i ∈ selected q batch kind) :
    position q batch kind i ∈ batchPositions batch ∧
      index q kind (position q batch kind i) = i := by
  obtain ⟨pos,hp,he⟩ := List.mem_map.mp hi
  have hs : ((batchPositions batch).find? (fun pos => decide (index q kind pos = i))).isSome :=
    List.find?_isSome.mpr ⟨pos,hp,by simpa only [he,decide_true]⟩
  cases hf : (batchPositions batch).find? (fun pos => decide (index q kind pos = i)) with
  | none => simp only [hf,Option.isSome_none] at hs; contradiction
  | some found =>
    have hm := List.mem_of_find?_eq_some hf
    have hk := of_decide_eq_true (List.find?_some hf)
    simpa only [position,hf,Option.getD_some] using And.intro hm hk

def representatives (q : Fin 22 → Fin 262144) (batch kind : Nat) : Finset Nat :=
  (batchPositions batch).toFinset.filter
    (fun pos => pos = position q batch kind (index q kind pos))

theorem representative_card (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    (representatives q batch kind).card = (selected q batch kind).toFinset.card := by
  apply Finset.card_bij (fun pos _ => index q kind pos)
  · intro pos hp
    have hm := (Finset.mem_filter.mp hp).1
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨pos,List.mem_toFinset.mp hm,rfl⟩)
  · intro a ha b hb he
    have hpa := (Finset.mem_filter.mp ha).2
    have hpb := (Finset.mem_filter.mp hb).2
    exact hpa.trans ((congrArg (position q batch kind) he).trans hpb.symm)
  · intro i hi
    have hr := representative q batch kind i (List.mem_toFinset.mp hi)
    refine ⟨position q batch kind i,?_,hr.2⟩
    apply Finset.mem_filter.mpr
    exact ⟨List.mem_toFinset.mpr hr.1,congrArg (position q batch kind) hr.2.symm⟩

theorem batch_nodup (batch : Nat) : (batchPositions batch).Nodup := by
  unfold batchPositions
  split
  · exact List.nodup_range
  · exact List.Nodup.map (fun a b h => by omega) List.nodup_range

theorem partition_count (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    (selected q batch kind).toFinset.card + (duplicatePositions q batch kind).length =
      (batchPositions batch).length := by
  rw [← representative_card]
  have hrep : (representatives q batch kind).card =
      ((batchPositions batch).filter
        (fun pos => decide (pos = position q batch kind (index q kind pos)))).length := by
    rw [representatives,← List.toFinset_filter]
    exact List.toFinset_card_of_nodup ((batch_nodup batch).filter _)
  rw [hrep]
  exact List.length_filter_add_length_filter_neg_eq_length _ _

theorem slot_leaf_law (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) :
    leaves (tree p q batch kind) + (duplicatePositions q batch kind).length =
      (batchPositions batch).length := by
  rw [tree,OraclePortSparseLeafCountC3.leaves_distinct]
  · exact partition_count q batch kind
  · intro i hi
    obtain ⟨pos,_,rfl⟩ := List.mem_map.mp hi
    unfold index
    split
    · have ht := (q ⟨pos % 22,Nat.mod_lt _ (by decide)⟩).isLt
      omega
    · exact (q _).isLt

#print axioms representative
#print axioms representative_card
#print axioms batch_nodup
#print axioms partition_count
#print axioms slot_leaf_law
end AspisR1.OraclePortRepresentativeCountC3
end
