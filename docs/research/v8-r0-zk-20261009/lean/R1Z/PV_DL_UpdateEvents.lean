import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_UpdateEvents
set_option autoImplicit false
abbrev Block := Array U8 64#usize
structure Plumbing where
  buffer : Block
  pos : Usize
  events : List Block

/-- The state-independent byte-buffer transition. Compression events are
recorded in source order; compression itself remains an explicit parameter. -/
def step (q : Plumbing) (byte : U8) : Plumbing :=
  let buffer := q.buffer.set q.pos byte
  let pos := Usize.wrapping_add q.pos 1#usize
  if pos=64#usize then ⟨buffer,0#usize,q.events++[buffer]⟩
  else ⟨buffer,pos,q.events⟩

def fold (q : Plumbing) (bytes : List U8) : Plumbing := bytes.foldl step q

theorem append (q : Plumbing) (a b : List U8) :
    fold q (a++b)=fold (fold q a) b := List.foldl_append

theorem complete (q : Plumbing) (byte : U8)
    (h : Usize.wrapping_add q.pos 1#usize=64#usize) :
    (step q byte).events=q.events++[q.buffer.set q.pos byte] := by
  simp only [step,h,if_true]

theorem pending (q : Plumbing) (byte : U8)
    (h : Usize.wrapping_add q.pos 1#usize≠64#usize) :
    (step q byte).events=q.events := by
  simp only [step,if_neg h]

#print axioms Plumbing
#print axioms step
#print axioms fold
#print axioms append
#print axioms complete
#print axioms pending
end R1Z.PV_DL_UpdateEvents
