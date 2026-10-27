import R1Z.PV_Src_PortEnumerateTrace

set_option autoImplicit false
namespace R1Z.PV_Src_PortEnumerateValues
open Aeneas Aeneas.Std
variable {A : Type}

theorem values (xs : List A) (count : Usize) (p : Usize × A)
    (hp : p ∈ PV_Src_PortEnumerateTrace.pairs xs count) : p.2 ∈ xs := by
  induction xs generalizing count with
  | nil => simp only [PV_Src_PortEnumerateTrace.pairs,List.not_mem_nil] at hp
  | cons x xs ih =>
    change p ∈ (count,x)::PV_Src_PortEnumerateTrace.pairs xs (Usize.wrapping_add count 1#usize) at hp
    rcases List.mem_cons.mp hp with he | ht
    · rw [he]
      exact List.mem_cons_self
    · exact List.mem_cons.mpr (Or.inr (ih _ ht))

#print axioms values
end R1Z.PV_Src_PortEnumerateValues
