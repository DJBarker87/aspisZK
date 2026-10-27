import R1Z.PV_AL_MoveLast
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_MoveNativeValue
set_option autoImplicit false

/-- Initialized backing slots are separate from the live vector header. -/
def readSlot {T : Type} (backing : alloc.vec.Vec T) (i : Usize) : Result T :=
  match backing.val[i.val]? with | none => fail .undef | some x => ok x

def shorten {T : Type} (backing : alloc.vec.Vec T) (i : Usize) : alloc.vec.Vec T :=
  ⟨backing.val.take i.val,by
    rw [List.length_take]
    exact le_trans (Nat.min_le_right _ _) backing.property⟩

/-- Structural library interpretation of frozen Vec::pop: decrement the live
header, check capacity, then read the last initialized backing slot. -/
def nativeValue {T : Type} (backing : alloc.vec.Vec T) (capacity : Nat) :
    Result (Option T × alloc.vec.Vec T) := do
  let n := alloc.vec.Vec.len backing
  if n=0#usize then ok (none,backing) else
    let last := Usize.wrapping_sub n 1#usize
    let remaining := shorten backing last
    if last.val < capacity then
      let x ← readSlot backing last
      ok (some x,remaining)
    else fail .undef

theorem source {T : Type} (v : alloc.vec.Vec T) (capacity : Nat)
    (fits : v.val.length ≤ capacity) :
    nativeValue v capacity=PV_CBL_VectorPopSpec.reference v := by
  by_cases h : v.val=[]
  · have hv : v=alloc.vec.Vec.new T := Subtype.ext h
    subst v
    rfl
  · have hn : alloc.vec.Vec.len v ≠ 0#usize := by
      intro hz
      have hl := congrArg (fun n : Usize => n.val) hz
      change v.val.length=0 at hl
      exact h (List.eq_nil_of_length_eq_zero hl)
    have hi := PV_AL_MoveFacts.last_value v h
    have hb := PV_AL_MoveFacts.last_bound v h
    have hc : v.val.length - 1 < capacity := by omega
    simp only [nativeValue,if_neg hn,readSlot,hi,if_pos hc,List.getElem?_eq_getElem hb,bind_tc_ok,
      PV_CBL_VectorPopSpec.reference]
    apply congrArg Result.ok
    apply Prod.ext
    · exact (PV_AL_PopLast.last v.val h).symm
    · apply Subtype.ext
      simp only [shorten,hi,PV_CBL_VectorPopSpec.pop,List.dropLast_eq_take]

theorem reference {T : Type} (v : alloc.vec.Vec T) (capacity : Nat)
    (fits : v.val.length ≤ capacity) :
    nativeValue v capacity=PV_AL_RemoveModel.pop_move_reference v := by
  rw [source v capacity fits,PV_AL_MoveLast.source]

#print axioms readSlot
#print axioms shorten
#print axioms nativeValue
#print axioms source
#print axioms reference
end R1Z.PV_AL_MoveNativeValue
