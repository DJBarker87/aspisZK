import S9MarkedSliceUpdateV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9TensorIndexedMeaningV1
open AspisR1S9MarkedSliceUpdateV1

def MeaningOn {Q E : Type} (decode : Q → E) (expected : Nat → E)
    (marked : Nat → Prop) (s : Slice Q) : Prop :=
  ∀ (i : Usize) (v : Q), Slice.index_usize s i = .ok v →
    marked i.val → decode v = expected i.val

theorem meaning_mono {Q E : Type} (decode : Q → E) (expected : Nat → E)
    (a b : Nat → Prop) (s : Slice Q) (h : MeaningOn decode expected a s)
    (hab : ∀ i, b i → a i) : MeaningOn decode expected b s := by
  intro i v hr hi
  exact h i v hr (hab i.val hi)

/-- Indexed source-update semantics. An overwritten cell must have the right
value for its actual index; every retained marked cell is framed exactly. -/
theorem update_meaning_on {Q E : Type} (decode : Q → E) (expected : Nat → E)
    (oldMark newMark : Nat → Prop) (s out : Slice Q) (k : Usize) (v : Q)
    (hold : MeaningOn decode expected oldMark s)
    (hvalue : decode v = expected k.val)
    (hcover : ∀ i, newMark i → i = k.val ∨ oldMark i)
    (hupdate : Slice.update s k v = .ok out) :
    MeaningOn decode expected newMark out := by
  obtain ⟨hbound,hout⟩ := update_success_bound_set s out k v hupdate
  intro i q hread hmark
  rw [hout] at hread
  by_cases heq : i.val = k.val
  · have hs : Slice.index_usize (Slice.set s k v) i =
        Slice.index_usize (Slice.set s k v) k := by
      simp only [Slice.index_usize, Slice.getElem?_Usize_eq, heq]
    have hv : v = q := Result.ok.inj ((hs.trans (set_read_eq s k v hbound)).symm.trans hread)
    simpa only [←hv,heq] using hvalue
  · have hm : oldMark i.val := by
      rcases hcover i.val hmark with hi | hi
      · exact False.elim (heq hi)
      · exact hi
    have hr : Slice.index_usize s i = .ok q :=
      (set_read_ne s k i v (Ne.symm heq)).symm.trans hread
    exact hold i q hr hm

/-- Preserve a selected old meaning when an unrelated source cell is written. -/
theorem update_meaning_frame {Q E : Type} (decode : Q → E) (expected : Nat → E)
    (mark : Nat → Prop) (s out : Slice Q) (k : Usize) (v : Q)
    (hold : MeaningOn decode expected mark s)
    (haway : ∀ i, mark i → i ≠ k.val)
    (hupdate : Slice.update s k v = .ok out) :
    MeaningOn decode expected mark out := by
  obtain ⟨_,hout⟩ := update_success_bound_set s out k v hupdate
  intro i q hr hm
  rw [hout, set_read_ne s k i v (Ne.symm (haway i.val hm))] at hr
  exact hold i q hr hm

#print axioms meaning_mono
#print axioms update_meaning_on
#print axioms update_meaning_frame
end AspisR1S9TensorIndexedMeaningV1
