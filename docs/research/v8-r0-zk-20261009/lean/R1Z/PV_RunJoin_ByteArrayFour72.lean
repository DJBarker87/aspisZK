import R1Z.PV_RunJoin_FlatBytes35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteArrayFour72
open Aeneas Aeneas.Std

theorem complete {T : Type} (a : Array T 4#usize) :
    Array.make 4#usize
      [a.val[0]'(by rw [a.property];decide),a.val[1]'(by rw [a.property];decide),
       a.val[2]'(by rw [a.property];decide),a.val[3]'(by rw [a.property];decide)]=a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [Array.make,List.length_cons,List.length_nil,a.property]
  · intro i hi hi'
    have bound : i<4 := by simpa only [Array.make,List.length_cons,List.length_nil] using hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl <;> rfl

#print axioms complete
end R1Z.PV_RunJoin_ByteArrayFour72
