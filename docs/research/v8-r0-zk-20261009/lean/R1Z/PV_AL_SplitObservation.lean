import R1Z.PV_AL_SplitSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_SplitObservation
set_option autoImplicit false

def observe (v : Slice U8) (size : Usize) : Result (List U8 × List U8) := do
  let (blocks,tail) ← PV_AL_SplitFlat.split_flat_reference v size
    (alloc.vec.Vec.new U8) (alloc.vec.Vec.new U8)
  ok (blocks.val,tail.val)

def specification (v : Slice U8) (size : Usize) : Result (List U8 × List U8) :=
  if size.val=0 then fail .divisionByZero else
    ok (v.val.take ((v.val.length/size.val)*size.val),
        v.val.drop ((v.val.length/size.val)*size.val))

theorem positive (v : Slice U8) (size : Usize) (hs : size.val ≠ 0) :
    observe v size=ok (v.val.take ((v.val.length/size.val)*size.val),
      v.val.drop ((v.val.length/size.val)*size.val)) := by
  obtain ⟨blocks,tail,h,hb,ht⟩ := PV_AL_SplitSource.source v size hs
  simp only [observe,h,bind_tc_ok]
  exact congrArg Result.ok (Prod.ext hb ht)

theorem zero (v : Slice U8) :
    PV_AL_SplitFlat.split_flat_reference v 0#usize (alloc.vec.Vec.new U8)
      (alloc.vec.Vec.new U8)=fail .divisionByZero := rfl

theorem observe_zero (v : Slice U8) : observe v 0#usize=fail .divisionByZero := by
  unfold observe
  rw [zero]
  rfl

theorem complete (v : Slice U8) (size : Usize) :
    observe v size=specification v size := by
  by_cases hs : size.val=0
  · have he : size=0#usize := UScalar.eq_of_val_eq hs
    subst size
    rw [observe_zero]
    rfl
  · rw [positive v size hs]
    simp only [specification,hs,if_false]

#print axioms observe
#print axioms specification
#print axioms positive
#print axioms zero
#print axioms observe_zero
#print axioms complete
end R1Z.PV_AL_SplitObservation
