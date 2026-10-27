import R1Z.PV_CBL_VectorPopSpec
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_RemoveModel
set_option autoImplicit false

/-- Explicit library value semantics for native remove's read/memmove/set_len.
This declaration does not assert an Aeneas extraction of native raw pointers. -/
def remove {T : Type} (_A : Type) (v : alloc.vec.Vec T) (i : Usize) :
    Result (T × alloc.vec.Vec T) :=
  match v.val[i.val]? with
  | none => fail .panic
  | some x => ok (x,⟨v.val.take i.val ++ v.val.drop (i.val+1),by
      simp only [List.length_append,List.length_take,List.length_drop]
      have := v.property
      omega⟩)

/-- Body retained from the successful pinned borrowed extraction, with the
native remove external bound to the explicit library model above. -/
def pop_move_reference {T : Type} (v : alloc.vec.Vec T) :
    Result ((Option T) × alloc.vec.Vec T) := do
  let n := alloc.vec.Vec.len v
  if n=0#usize then ok (none,v) else
    let i ← lift (Usize.wrapping_sub n 1#usize)
    let (t,v1) ← remove Global v i
    ok (some t,v1)

#print axioms remove
#print axioms pop_move_reference
end R1Z.PV_AL_RemoveModel
