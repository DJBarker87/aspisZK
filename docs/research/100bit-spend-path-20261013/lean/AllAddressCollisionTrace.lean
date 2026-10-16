import AllAddressCollision

/-! The finite table-cover guard holds before every read in a consistent
bounded trace, regardless of address-space cardinality. Outside the event,
all outputs are distinct and parsed state targets must be read later. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AllAddressCollisionTrace

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisR1.AllAddressCollision

variable {I A : Type} [DecidableEq I] [Fintype A] [Inhabited A]

/-- First-read counting on the finite support of a trace; this does not
require the address type itself to be finite. -/
theorem firstReads_eq_card_finiteSupport : ∀ (tr : List (I × A)) (t : Table I A),
    firstReads t tr = ((tr.map Prod.fst).toFinset.filter fun a => t a = none).card := by
  classical
  intro tr
  induction tr with
  | nil => intro t; simp [firstReads]
  | cons q rest ih =>
      intro t
      obtain ⟨i, v⟩ := q
      simp only [firstReads, List.map_cons, List.toFinset_cons, ih (put t i v)]
      by_cases hi : t i = none
      · rw [if_pos hi]
        have hsplit : ((insert i (rest.map Prod.fst).toFinset).filter fun a => t a = none) =
            insert i (((rest.map Prod.fst).toFinset).filter fun a => put t i v a = none) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_insert, put]
          by_cases hai : a = i
          · subst hai; simp [hi]
          · simp [hai]
        rw [hsplit, Finset.card_insert_of_notMem]
        · ring
        · simp [put]
      · rw [if_neg hi]
        have hsplit : ((insert i (rest.map Prod.fst).toFinset).filter fun a => t a = none) =
            ((rest.map Prod.fst).toFinset).filter fun a => put t i v a = none := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_insert, put]
          by_cases hai : a = i
          · subst hai; simp [hi]
          · simp [hai]
        rw [hsplit]
        ring

theorem small_before_read (H : I → A) (tr : List (I × A)) (a : I)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (ha : Read tr a)
    (Q : Nat) (hQ : firstReads emptyTable tr ≤ Q) :
    Small (tableBefore emptyTable tr a) Q := by
  classical
  let s := (tr.map Prod.fst).toFinset.filter (fun b => Before tr b a)
  have hnot : a ∉ s := by
    simp only [s, Finset.mem_filter]
    exact fun h => before_irrefl tr a h.2
  have hcard : (insert a s).card ≤ (tr.map Prod.fst).toFinset.card := by
    apply Finset.card_le_card
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact List.mem_toFinset.mpr ha
    · exact (Finset.mem_filter.mp hb).1
  rw [Finset.card_insert_of_notMem hnot] at hcard
  have hcount : firstReads emptyTable tr = (tr.map Prod.fst).toFinset.card := by
    rw [firstReads_eq_card_finiteSupport]
    congr 1
    ext b
    simp [emptyTable]
  refine ⟨s, by omega, ?_⟩
  intro b hb
  rw [tableBefore_eq H tr emptyTable a b hcons] at hb
  have hbefore : Before tr b a := by
    by_contra h
    exact hb (by simp [h, emptyTable])
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hbefore.1, hbefore⟩

theorem outside_at_read {B : Nat} (iv : A) (pred : Fin B → I → Option A)
    (H : I → A) (tr : List (I × A)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (bad iv pred Q) emptyTable tr)
    (a : I) (ha : Read tr a) :
    H a ≠ iv ∧
      (∀ b, Before tr b a → H b ≠ H a) ∧
      (∀ j b, (b = a ∨ Before tr b a) → pred j b ≠ some (H a)) := by
  have hbad : ¬ bad iv pred Q a (tableBefore emptyTable tr a) (H a) := by
    intro hb
    exact hout (FS.hitsBad_of_first (bad iv pred Q) H a tr emptyTable hcons ha rfl hb)
  have hsmall := small_before_read H tr a hcons ha Q hQ
  refine ⟨fun h => hbad ⟨hsmall, Or.inl h⟩, ?_, ?_⟩
  · intro b hb he
    apply hbad
    refine ⟨hsmall, Or.inr (Or.inl ⟨b, ?_⟩)⟩
    rw [tableBefore_eq H tr emptyTable a b hcons, if_pos hb, he]
  · intro j b hb he
    apply hbad
    refine ⟨hsmall, Or.inr (Or.inr ⟨j, b, ?_, he⟩)⟩
    rcases hb with rfl | hb
    · exact Or.inl rfl
    · right
      rw [tableBefore_eq H tr emptyTable a b hcons, if_pos hb]
      exact Option.some_ne_none _

theorem outputs_injective {B : Nat} (iv : A) (pred : Fin B → I → Option A)
    (H : I → A) (tr : List (I × A)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (bad iv pred Q) emptyTable tr)
    (a b : I) (ha : Read tr a) (hb : Read tr b) (hne : a ≠ b) :
    H a ≠ H b := by
  rcases before_total tr a b ha hb hne with hab | hba
  · exact (outside_at_read iv pred H tr Q hcons hQ hout b hb).2.1 a hab
  · exact fun he => (outside_at_read iv pred H tr Q hcons hQ hout a ha).2.1 b hba he.symm

theorem parsed_target_after {B : Nat} (iv : A) (pred : Fin B → I → Option A)
    (H : I → A) (tr : List (I × A)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (bad iv pred Q) emptyTable tr)
    (j : Fin B) (a b : I) (ha : Read tr a) (hb : Read tr b)
    (hpred : pred j b = some (H a)) : Before tr a b := by
  have hne : a ≠ b := by
    intro h
    subst b
    exact (outside_at_read iv pred H tr Q hcons hQ hout a ha).2.2 j a (Or.inl rfl) hpred
  rcases before_total tr a b ha hb hne with hab | hba
  · exact hab
  · exact False.elim
      ((outside_at_read iv pred H tr Q hcons hQ hout a ha).2.2 j b (Or.inr hba) hpred)

#print axioms small_before_read
#print axioms outside_at_read
#print axioms outputs_injective
#print axioms parsed_target_after
end AspisR1.AllAddressCollisionTrace
end
