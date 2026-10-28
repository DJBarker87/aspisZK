import NBD_DigestInduction
set_option autoImplicit false
noncomputable section
namespace NBD_DigestTrace
open Aeneas Aeneas.Std Result
open NBD_DigestInduction
attribute [local instance] Classical.propDecidable

/-- Native one-iteration relation: no precondition on the words. -/
inductive Trace (word : Nat → Nat) : Nat → Nat → Bool → Prop where
  | done (i : Nat) : Trace word i 0 true
  | reject (i n : Nat) (bad : 2147483647 ≤ word i) : Trace word i (n+1) false
  | advance (i n : Nat) (b : Bool) (good : word i < 2147483647)
      (rest : Trace word (i+1) n b) : Trace word i (n+1) b

theorem exact (word : Nat → Nat) (i n : Nat) (b : Bool) (trace : Trace word i n b) :
    b = true ↔ ∀ j, i ≤ j → j < i+n → word j < 2147483647 := by
  induction trace with
  | done i => simp; omega
  | reject i n bad =>
    constructor
    · intro h; cases h
    · intro h
      have := h i (by omega) (by omega)
      omega
  | advance i n b good rest ih =>
    constructor
    · intro hb j lo hi
      by_cases same : j = i
      · simpa [same] using good
      · exact ih.mp hb j (by omega) (by omega)
    · intro h
      apply ih.mpr
      intro j lo hi
      exact h j (by omega) (by omega)

theorem total (word : Nat → Nat) (i n : Nat) : ∃ b, Trace word i n b := by
  induction n generalizing i with
  | zero => exact ⟨true, .done i⟩
  | succ n ih =>
    by_cases good : word i < 2147483647
    · obtain ⟨b,rest⟩ := ih (i+1)
      exact ⟨b,.advance i n b good rest⟩
    · exact ⟨false,.reject i n (by omega)⟩

def word (d : Array U32 8#usize) (i : Nat) : Nat :=
  if h : i < 8 then (d.val[i]'(by have := d.property; scalar_tac)).val else 0

theorem word_eq (d : Array U32 8#usize) (j : Nat) (hj : j < 8) :
    word d j = (d.val[j]'(by have := d.property; scalar_tac)).val := by
  simp only [word, dif_pos hj]

/-- Native step induction associated with the actual emitted Result, including rejection. -/
theorem native_result (d : Array U32 8#usize) (b : Bool)
    (trace : Trace (word d) 0 8 b) :
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical d = ok b ∧
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical d = ok b := by
  have assoc : (∀ j, 0 ≤ j → j < 0+8 → word d j < 2147483647) ↔ Canonical d := by
    constructor
    · intro h j
      have := h j.val (by omega) j.isLt
      simpa only [word_eq d j.val j.isLt] using this
    · intro h j _ hj
      rw [word_eq d j hj]
      exact h ⟨j,hj⟩
  have same : b = decide (Canonical d) := by
    have h := (exact _ _ _ _ trace).trans assoc
    cases b <;> simp_all
  have first := NBD_DigestInduction.source d
  rw [←same] at first
  exact ⟨first,(same_scanner d).trans first⟩

#print axioms exact
#print axioms total
#print axioms word_eq
#print axioms native_result
end NBD_DigestTrace
