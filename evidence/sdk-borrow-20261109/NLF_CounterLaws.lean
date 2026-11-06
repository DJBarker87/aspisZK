import NLF_Drop
set_option autoImplicit false
namespace NLF_CounterLaws
open NLF_RefCell

theorem erase_length (xs : List Nat) (t : Nat) (ht : t∈xs) :
    (xs.erase t).length+1 = xs.length := by
  induction xs with
  | nil => simp at ht
  | cons a xs ih =>
    by_cases eq : a=t
    · subst a; simp
    · have mem : t∈xs := by simpa [eq,Ne.symm eq] using ht
      simp [List.erase_cons,eq,Ne.symm eq,ih mem]

theorem shared_current_counter {α : Type} (c : Cell α) (t : Nat)
    (h : live c t .shared) :
    flag {c with readers:=c.readers.erase t} = flag c - 1 := by
  have len := erase_length c.readers t h.2
  simp only [flag,h.1,Int.ofNat_eq_natCast]
  omega

theorem exclusive_zero {α : Type} (c : Cell α) (t : Nat)
    (v : Valid c) (h : live c t .exclusive) :
    flag {c with writer:=none} = 0 := by
  have readers : c.readers=[] := v.2 (by simp only [live] at h; simp [h])
  simp [flag,readers]

theorem shared_positive {α : Type} (c : Cell α) (t : Nat)
    (h : live c t .shared) : 0 < flag c := by
  have nonempty : c.readers ≠ [] := by intro eq; simpa [eq] using h.2
  simp only [flag,h.1,Int.ofNat_eq_natCast]
  cases hr : c.readers with
  | nil => simp [hr] at nonempty
  | cons a xs => simp [hr]

theorem exclusive_negative {α : Type} (c : Cell α) (t : Nat)
    (h : live c t .exclusive) : flag c = -1 := by simp [flag,live] at h ⊢; rw [h]

#print axioms erase_length
#print axioms shared_current_counter
#print axioms exclusive_zero
#print axioms shared_positive
#print axioms exclusive_negative
end NLF_CounterLaws
