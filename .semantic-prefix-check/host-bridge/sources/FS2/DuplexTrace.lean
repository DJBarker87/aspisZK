import FS2.DuplexInj
import FS2.Verifier

/-! # Trace calculus and the consequences of the collision event

For a consistent trace (every entry carries the oracle's value):
`firstIdx a` is the position of `a`'s first read, `Before b a` says `b` was
first-read before `a`; `tableBefore ∅ tr a` holds exactly the cells first-read
before `a`, with the oracle's values.  The number of distinct first reads
bounds the size of every such table.

Outside the collision event, for every read address `a`: its output is not
`iv`, differs from the output of every other read address, and its bytes are
not a 32-byte prefix of `a` or of any address read before `a`. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

section Trace
variable {I A : Type} [DecidableEq I]

def firstIdx (a : I) : List (I × A) → Nat
  | [] => 0
  | (i, _) :: rest => if i = a then 0 else firstIdx a rest + 1

def Read (tr : List (I × A)) (a : I) : Prop := a ∈ tr.map Prod.fst

instance (tr : List (I × A)) (a : I) : Decidable (Read tr a) :=
  inferInstanceAs (Decidable (a ∈ tr.map Prod.fst))

/-- `b` is first-read before `a`'s first read (or `a` is never read). -/
def Before (tr : List (I × A)) (b a : I) : Prop := Read tr b ∧ firstIdx b tr < firstIdx a tr

instance (tr : List (I × A)) (b a : I) : Decidable (Before tr b a) :=
  inferInstanceAs (Decidable (Read tr b ∧ firstIdx b tr < firstIdx a tr))

theorem firstIdx_lt_length (a : I) : ∀ tr : List (I × A), Read tr a → firstIdx a tr < tr.length := by
  intro tr
  induction tr with
  | nil => intro h; simp [Read] at h
  | cons q rest ih =>
      intro h
      obtain ⟨i, v⟩ := q
      simp only [firstIdx, List.length_cons]
      by_cases hi : i = a
      · simp [hi]
      · rw [if_neg hi]
        have : Read rest a := by
          simp only [Read, List.map_cons, List.mem_cons] at h
          exact (h.resolve_left (Ne.symm hi))
        have := ih this
        omega

theorem firstIdx_eq_length (a : I) : ∀ tr : List (I × A), ¬ Read tr a → firstIdx a tr = tr.length := by
  intro tr
  induction tr with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro h
      obtain ⟨i, v⟩ := q
      have hi : i ≠ a := fun e => h (by simp [Read, e])
      have hr : ¬ Read rest a := fun hr => h (by simp only [Read, List.map_cons, List.mem_cons]; exact Or.inr hr)
      simp [firstIdx, hi, ih hr]

/-- The table before `a`'s first read: the cells first-read before `a`, with
the oracle's values. -/
theorem tableBefore_eq (H : I → A) :
    ∀ (tr : List (I × A)) (t : Table I A) (a b : I), (∀ q ∈ tr, q.2 = H q.1) →
      tableBefore t tr a b = if Before tr b a then some (H b) else t b := by
  intro tr
  induction tr with
  | nil => intro t a b _; simp [tableBefore, Before, Read]
  | cons q rest ih =>
      intro t a b hcons
      obtain ⟨i, v⟩ := q
      have hv : v = H i := hcons (i, v) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      simp only [tableBefore]
      by_cases hia : i = a
      · subst hia
        rw [if_pos rfl]
        have : ¬ Before ((i, v) :: rest) b i := by
          rintro ⟨_, hlt⟩
          simp [firstIdx] at hlt
        rw [if_neg this]
      · rw [if_neg hia, ih (put t i v) a b hrest]
        by_cases hib : i = b
        · subst hib
          have hB : Before ((i, v) :: rest) i a := by
            refine ⟨by simp [Read], ?_⟩
            simp [firstIdx, hia]
          rw [if_pos hB]
          split
          · rfl
          · simp [put, hv]
        · have hiff : Before rest b a ↔ Before ((i, v) :: rest) b a := by
            simp only [Before, Read, List.map_cons, List.mem_cons, firstIdx, hia, hib, if_false]
            constructor
            · rintro ⟨hr, hlt⟩; exact ⟨Or.inr hr, by omega⟩
            · rintro ⟨hr, hlt⟩
              exact ⟨hr.resolve_left (Ne.symm hib), by omega⟩
          by_cases hB : Before rest b a
          · rw [if_pos hB, if_pos (hiff.mp hB)]
          · rw [if_neg hB, if_neg (fun h => hB (hiff.mpr h))]
            simp [put, Ne.symm hib]

theorem tableBefore_self (H : I → A) (tr : List (I × A)) (a : I) (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    tableBefore emptyTable tr a a = none := by
  rw [tableBefore_eq H tr emptyTable a a hcons]
  have : ¬ Before tr a a := fun ⟨_, h⟩ => lt_irrefl _ h
  rw [if_neg this]; rfl

/-- Two distinct read addresses are ordered. -/
theorem before_total (tr : List (I × A)) (a b : I) (ha : Read tr a) (hb : Read tr b) (hne : a ≠ b) :
    Before tr a b ∨ Before tr b a := by
  have : firstIdx a tr ≠ firstIdx b tr := by
    intro h
    revert ha hb
    induction tr with
    | nil => intro ha; simp [Read] at ha
    | cons q rest ih =>
        intro ha hb
        obtain ⟨i, v⟩ := q
        simp only [firstIdx] at h
        by_cases hia : i = a
        · subst hia
          by_cases hib : i = b
          · exact hne hib
          · simp [hib] at h
        · by_cases hib : i = b
          · subst hib; simp [hia] at h
          · simp only [hia, hib, if_false, Nat.add_right_cancel_iff] at h
            apply ih h
            · simp only [Read, List.map_cons, List.mem_cons] at ha; exact ha.resolve_left (Ne.symm hia)
            · simp only [Read, List.map_cons, List.mem_cons] at hb; exact hb.resolve_left (Ne.symm hib)
  rcases Nat.lt_or_gt_of_ne this with h | h
  · exact Or.inl ⟨ha, h⟩
  · exact Or.inr ⟨hb, h⟩

theorem before_trans (tr : List (I × A)) {a b c : I} (h1 : Before tr a b) (h2 : Before tr b c) :
    Before tr a c := ⟨h1.1, lt_trans h1.2 h2.2⟩

theorem before_irrefl (tr : List (I × A)) (a : I) : ¬ Before tr a a := fun ⟨_, h⟩ => lt_irrefl _ h

theorem before_ne (tr : List (I × A)) {a b : I} (h : Before tr a b) : a ≠ b := by
  intro e; subst e; exact before_irrefl tr a h

end Trace

/-! ## First-read count bounds every table's size -/

section Count
variable {I A : Type} [DecidableEq I] [Fintype I] [Fintype A] [DecidableEq A] [Nonempty A]

theorem firstReads_eq_card : ∀ (tr : List (I × A)) (t : Table I A),
    firstReads t tr = ((tr.map Prod.fst).toFinset.filter fun a => t a = none).card := by
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

theorem dom_tableBefore_subset (H : I → A) (tr : List (I × A)) (a : I)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    dom (tableBefore emptyTable tr a) ⊆ (tr.map Prod.fst).toFinset := by
  intro b hb
  rw [dom, Finset.mem_filter] at hb
  rw [tableBefore_eq H tr emptyTable a b hcons] at hb
  split at hb
  · rename_i hB
    exact List.mem_toFinset.mpr hB.1
  · exact absurd rfl hb.2

theorem a_notMem_dom (H : I → A) (tr : List (I × A)) (a : I) (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    a ∉ dom (tableBefore emptyTable tr a) := by
  rw [dom, Finset.mem_filter, tableBefore_self H tr a hcons]
  simp

theorem card_dom_lt (H : I → A) (tr : List (I × A)) (a : I) (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (ha : Read tr a) (Qtot : Nat) (hQ : firstReads emptyTable tr ≤ Qtot) :
    (dom (tableBefore emptyTable tr a)).card < Qtot := by
  have h1 : (insert a (dom (tableBefore emptyTable tr a))).card ≤ (tr.map Prod.fst).toFinset.card := by
    apply Finset.card_le_card
    intro b hb
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact List.mem_toFinset.mpr ha
    · exact dom_tableBefore_subset H tr a hcons hb
  rw [Finset.card_insert_of_notMem (a_notMem_dom H tr a hcons)] at h1
  have h2 : firstReads emptyTable tr = (tr.map Prod.fst).toFinset.card := by
    rw [firstReads_eq_card]
    congr 1
    ext b
    simp [emptyTable]
  omega

end Count

/-! ## Consequences of the collision event -/

variable {M Cv : Type} {L : Nat}

set_option linter.constructorNameAsVariable false in
/-- Outside the collision event, every read address satisfies the three
non-collision facts. -/
theorem noColl (p : Params M Cv L) (Qtot : Nat) (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr) (a : Addr L) (ha : Read tr a) :
    H a ≠ p.iv ∧
    (∀ b, Before tr b a → H b ≠ H a) ∧
    (∀ b, (b = a ∨ Before tr b a) → b.toBytes.take 32 ≠ bytes (H a)) := by
  have hbad : ¬ badColl p Qtot a (tableBefore emptyTable tr a) (H a) := by
    intro hb
    exact hcoll (FS.hitsBad_of_first (badColl p Qtot) H a tr emptyTable hcons ha rfl hb)
  have hsz := card_dom_lt H tr a hcons ha Qtot hQ
  refine ⟨fun e => hbad (badColl_of_iv p Qtot a _ _ hsz e), ?_, ?_⟩
  · intro b hB e
    apply hbad
    apply badColl_of_output p Qtot a _ _ hsz b
    rw [tableBefore_eq H tr emptyTable a b hcons, if_pos hB, e]
  · intro b hb e
    apply hbad
    apply badColl_of_prefix p Qtot a _ _ hsz b _ e
    rcases hb with rfl | hB
    · exact Or.inl rfl
    · right
      rw [tableBefore_eq H tr emptyTable a b hcons, if_pos hB]
      exact Option.some_ne_none _

/-- Distinct read addresses have distinct outputs. -/
theorem noColl_injective (p : Params M Cv L) (Qtot : Nat) (H : Addr L → State)
    (tr : List (Addr L × State)) (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot) (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (a b : Addr L) (ha : Read tr a) (hb : Read tr b) (hne : a ≠ b) : H a ≠ H b := by
  rcases before_total tr a b ha hb hne with h | h
  · exact (noColl p Qtot H tr hcons hQ hcoll b hb).2.1 a h
  · exact fun e => (noColl p Qtot H tr hcons hQ hcoll a ha).2.1 b h e.symm

/-- An address whose 32-byte prefix is a read address's output is read
strictly after it. -/
theorem noColl_prefix_after (p : Params M Cv L) (Qtot : Nat) (H : Addr L → State)
    (tr : List (Addr L × State)) (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot) (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (a b : Addr L) (ha : Read tr a) (hb : Read tr b) (hpre : b.toBytes.take 32 = bytes (H a)) :
    Before tr a b := by
  have hne : b ≠ a := by
    intro e; subst e
    exact (noColl p Qtot H tr hcons hQ hcoll b hb).2.2 b (Or.inl rfl) hpre
  rcases before_total tr a b ha hb (Ne.symm hne) with h | h
  · exact h
  · exact absurd hpre ((noColl p Qtot H tr hcons hQ hcoll a ha).2.2 b (Or.inr h))

end
end FS2.Duplex
