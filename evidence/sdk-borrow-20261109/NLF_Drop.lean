import NLF_RefCell
set_option autoImplicit false
namespace NLF_RefCell

theorem shared_drop_roundtrip {α : Type} (c : Cell α) (t : Nat)
    (fresh : t ∉ c.readers) (free : c.writer = none) :
    dropShared {c with readers := t :: c.readers} t = .ok c := by
  cases c with | mk p r w => simp_all [dropShared]

theorem exclusive_drop_roundtrip {α : Type} (c : Cell α) (t : Nat)
    (free : c.writer = none) :
    dropExclusive {c with writer := some t} t = .ok c := by
  cases c with | mk p r w => simp_all [dropExclusive]

theorem shared_drop_valid {α : Type} (c : Cell α) (t : Nat) (v : Valid c)
    (live : live c t .shared) :
    dropShared c t = .ok {c with readers := c.readers.erase t} ∧
    Valid {c with readers := c.readers.erase t} := by
  constructor
  · simp [dropShared, live.1, live.2]
  · exact ⟨v.1.erase t, by simp [live.1]⟩

theorem exclusive_drop_valid {α : Type} (c : Cell α) (t : Nat) (v : Valid c)
    (live : live c t .exclusive) :
    dropExclusive c t = .ok {c with writer := none} ∧
    Valid {c with writer := none} := by
  constructor
  · simp [dropExclusive, NLF_RefCell.live] at live ⊢; exact live
  · exact ⟨v.1, by simp⟩

theorem no_double_exclusive {α : Type} (c : Cell α) (s t : Nat)
    (hs : live c s .exclusive) (ht : live c t .exclusive) : s = t := by
  simp only [live] at hs ht
  exact Option.some.inj (hs.symm.trans ht)

theorem writer_excludes_readers {α : Type} (c : Cell α) (s t : Nat)
    (hs : live c s .exclusive) : ¬ live c t .shared := by
  simp only [live] at hs ⊢
  simp [hs]

theorem drop_shared_consumes {α : Type} (c : Cell α) (t : Nat) (v : Valid c) :
    t ∉ c.readers.erase t := by
  have aux : ∀ (xs : List Nat), xs.Nodup → t ∉ xs.erase t := by
    intro xs hn
    induction xs with
    | nil => simp
    | cons a xs ih =>
      rcases List.nodup_cons.mp hn with ⟨ha, hxs⟩
      by_cases h : a = t
      · subst a; simpa using ha
      · simp [List.erase_cons, h, Ne.symm h, ih hxs]
  exact aux c.readers v.1

theorem drop_exclusive_consumes {α : Type} (c : Cell α) (t : Nat) :
    ¬ live {c with writer := none} t .exclusive := by simp [live]

theorem shared_counter_acquire {α : Type} (c : Cell α) (t : Nat)
    (free : c.writer = none) :
    flag {c with readers := t :: c.readers} = flag c + 1 := by
  simp [flag, free, Int.natCast_add]

theorem exclusive_counter {α : Type} (c : Cell α) (t : Nat) :
    flag {c with writer := some t} = -1 := rfl

#print axioms shared_drop_roundtrip
#print axioms exclusive_drop_roundtrip
#print axioms shared_drop_valid
#print axioms exclusive_drop_valid
#print axioms no_double_exclusive
#print axioms writer_excludes_readers
#print axioms drop_shared_consumes
#print axioms drop_exclusive_consumes
#print axioms shared_counter_acquire
#print axioms exclusive_counter
end NLF_RefCell
