import OraclePortCoverageDraft

/-! Cardinality transport through occupied binary subtrees. All proofs are
symbolic in height; no concrete leaf universe is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSparseLeafCountC3
open OracleDecisionMultiTree OracleDecisionMultiBuild
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

def cells (is : List Nat) (h base : Nat) : Finset Nat :=
  is.toFinset.filter (fun i => base ≤ i ∧ i < base+2^h)

theorem cells_nonempty (is : List Nat) (h base : Nat) :
    (cells is h base).Nonempty ↔ Occupied is h base := by
  simp only [cells,Finset.nonempty_def,Finset.mem_filter,List.mem_toFinset,Occupied]
  aesop

theorem cells_split (is : List Nat) (h base : Nat) :
    cells is (h+1) base = cells is h base ∪ cells is h (base+2^h) := by
  ext i
  simp only [cells,Finset.mem_filter,List.mem_toFinset,Finset.mem_union,Nat.pow_succ]
  omega

theorem cells_disjoint (is : List Nat) (h base : Nat) :
    Disjoint (cells is h base) (cells is h (base+2^h)) := by
  apply Finset.disjoint_left.mpr
  intro i hl hr
  simp only [cells,Finset.mem_filter] at hl hr
  omega

theorem leaves_card (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (h base : Nat) : leaves (build is f s h base) = (cells is h base).card := by
  induction h generalizing base with
  | zero =>
    by_cases ho : Occupied is 0 base
    · have hc : cells is 0 base = {base} := by
        have hb := (occupied_zero is base).mp ho
        ext i
        simp only [cells,Finset.mem_filter,List.mem_toFinset,pow_zero,Finset.mem_singleton]
        constructor
        · intro hh; omega
        · intro hh; subst i; exact ⟨hb,le_rfl,by omega⟩
      rw [build,if_pos ho,leaves,hc,Finset.card_singleton]
    · have hc : cells is 0 base = ∅ := Finset.not_nonempty_iff_eq_empty.mp
        (fun hn => ho ((cells_nonempty is 0 base).mp hn))
      rw [build,if_neg ho,leaves,hc,Finset.card_empty]
  | succ h ih =>
    by_cases ho : Occupied is (h+1) base
    · rw [build,if_pos ho,leaves,ih,ih,cells_split,
        Finset.card_union_of_disjoint (cells_disjoint is h base)]
    · have hc : cells is (h+1) base = ∅ := Finset.not_nonempty_iff_eq_empty.mp
        (fun hn => ho ((cells_nonempty is (h+1) base).mp hn))
      rw [build,if_neg ho,leaves,hc,Finset.card_empty]

theorem leaves_distinct (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (h : Nat) (bound : ∀ i ∈ is, i < 2^h) :
    leaves (build is f s h 0) = is.toFinset.card := by
  rw [leaves_card]
  congr 1
  ext i
  simp only [cells,Finset.mem_filter,List.mem_toFinset,Nat.zero_add]
  exact ⟨fun hi => hi.1,fun hi => ⟨hi,Nat.zero_le _,bound i hi⟩⟩

#print axioms cells_nonempty
#print axioms cells_split
#print axioms cells_disjoint
#print axioms leaves_card
#print axioms leaves_distinct
end AspisR1.OraclePortSparseLeafCountC3
end
