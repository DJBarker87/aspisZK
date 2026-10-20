import OracleDecisionMultiTree

/-! Recompute the occupied subtree from the public query indices. There is
no caller-supplied schedule of parent hashes. Unoccupied subtrees consume
supplied sibling values; opened positions are determined by the indices.
Repeated indices select one leaf input; source duplicate equality checks and
extra leaf calls remain the boundary represented in MultiTree. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiBuild
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree

/-- `base` is the left endpoint of a subtree with `2^height` leaves. -/
def Occupied (indices : List Nat) (height base : Nat) : Prop :=
  ∃ i ∈ indices, base ≤ i ∧ i < base + 2^height

instance (indices : List Nat) (height base : Nat) : Decidable (Occupied indices height base) :=
  inferInstanceAs (Decidable (∃ i ∈ indices, base ≤ i ∧ i < base + 2^height))

def build (indices : List Nat) (input : Nat → Bytes) (sibling : Nat → Nat → State) :
    Nat → Nat → Tree
  | 0, base => if Occupied indices 0 base then .opened (input base)
      else .supplied (sibling 0 base)
  | h+1, base => if Occupied indices (h+1) base then
      .branch (build indices input sibling h base)
        (build indices input sibling h (base + 2^h))
      else .supplied (sibling (h+1) base)

theorem occupied_split (indices : List Nat) (h base : Nat) :
    Occupied indices (h+1) base ↔
      Occupied indices h base ∨ Occupied indices h (base + 2^h) := by
  simp only [Occupied, Nat.pow_succ]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    by_cases hm : i < base + 2^h
    · exact Or.inl ⟨i, hi, hlo, hm⟩
    · exact Or.inr ⟨i, hi, by omega, by omega⟩
  · rintro (⟨i, hi, hlo, hhi⟩ | ⟨i, hi, hlo, hhi⟩)
    · exact ⟨i, hi, hlo, by omega⟩
    · exact ⟨i, hi, by omega, by omega⟩

theorem leaves_positive_iff (indices : List Nat) (input : Nat → Bytes)
    (sibling : Nat → Nat → State) (h base : Nat) :
    0 < leaves (build indices input sibling h base) ↔ Occupied indices h base := by
  induction h generalizing base with
  | zero => by_cases ho : Occupied indices 0 base <;> simp [build, ho, leaves]
  | succ h ih =>
      by_cases ho : Occupied indices (h+1) base
      · simp only [build, if_pos ho, leaves]
        have hs := (occupied_split indices h base).mp ho
        have hl := ih base
        have hr := ih (base + 2^h)
        constructor
        · intro _; exact ho
        · intro _; rcases hs with hs | hs
          · have := hl.mpr hs; omega
          · have := hr.mpr hs; omega
      · simp [build, ho, leaves]

theorem build_minimal (indices : List Nat) (input : Nat → Bytes)
    (sibling : Nat → Nat → State) (h base : Nat) :
    OracleDecisionMultiTree.Minimal (build indices input sibling h base) := by
  induction h generalizing base with
  | zero => by_cases ho : Occupied indices 0 base <;> simp [build, ho, OracleDecisionMultiTree.Minimal]
  | succ h ih =>
      by_cases ho : Occupied indices (h+1) base
      · simp only [build, if_pos ho, OracleDecisionMultiTree.Minimal]
        refine ⟨ih base, ih (base + 2^h), ?_⟩
        rcases (occupied_split indices h base).mp ho with hl | hr
        · have := (leaves_positive_iff indices input sibling h base).mpr hl; omega
        · have := (leaves_positive_iff indices input sibling h (base + 2^h)).mpr hr; omega
      · simp [build, ho, OracleDecisionMultiTree.Minimal]

/-- Exactly one opened node at height zero iff the public index is present.
The tree never hashes any leaf outside the query set. -/
theorem occupied_zero (indices : List Nat) (base : Nat) :
    Occupied indices 0 base ↔ base ∈ indices := by
  simp only [Occupied, pow_zero]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    have : i = base := by omega
    simpa [this] using hi
  · intro hi; exact ⟨base, hi, le_rfl, by omega⟩

/-- Six checked fixed slots imply the weaker summed condition used by the
budget theorem. These are literally the deployed compact-format capacities. -/
theorem fixed_slots (a b c d e f : Commitment)
    (ha : siblings a.tree ≤ 146) (hb : siblings b.tree ≤ 146)
    (hc : siblings c.tree ≤ 128) (hd : siblings d.tree ≤ 172)
    (he : siblings e.tree ≤ 172) (hf : siblings f.tree ≤ 150) :
    totalSiblings [a,b,c,d,e,f] ≤ 914 := by
  simp only [totalSiblings, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

#print axioms occupied_split
#print axioms leaves_positive_iff
#print axioms build_minimal
#print axioms occupied_zero
#print axioms fixed_slots
end AspisR1.OracleDecisionMultiBuild
end
