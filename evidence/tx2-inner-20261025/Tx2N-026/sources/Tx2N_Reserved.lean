import Tx2N_Header
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Reserved
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Ops

theorem zeros (s : Slice U8) (rest : core.slice.iter.Iter U8)
    (size : s.val.length = 5)
    (scan : headerAny ⟨s,0⟩ = ok (false,rest)) : s.val = List.replicate 5 0#u8 := by
  rcases s with ⟨xs,bound⟩
  rcases xs with _ | ⟨x0,xs⟩
  · simp at size
  rcases xs with _ | ⟨x1,xs⟩
  · simp at size
  rcases xs with _ | ⟨x2,xs⟩
  · simp at size
  rcases xs with _ | ⟨x3,xs⟩
  · simp at size
  rcases xs with _ | ⟨x4,xs⟩
  · simp at size
  have last : xs = [] := List.length_eq_zero.mp (by simpa using size)
  subst xs
  simp_all [headerAny,headerLoop,core.slice.iter.IteratorSliceIter.next]

#print axioms zeros
end AspisR1.Tx2N_Reserved
end
