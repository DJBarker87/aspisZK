import R1Z.PV_CBL_DigestSoft
import R1Z.PV_CBL_ArrayMutableValue
import R1Z.PV_CBL_ArrayStep
import R1Z.PV_CBL_SoftByteExtracted
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_DigestUpdateStep
set_option autoImplicit false
abbrev Snapshot := Array U32 8#usize × U64 × Array U8 64#usize × Usize
def next (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (byte : U8) : Snapshot :=
  let buffer := buffer.set pos byte
  let pos1 := Usize.wrapping_add pos 1#usize
  if pos1=64#usize then
    (PV_CBL_SoftByteSource.value state buffer,U64.wrapping_add blocks 1#u64,buffer,0#usize)
  else (state,blocks,buffer,pos1)
def continuing (q : Snapshot) (j : Usize) :
    ControlFlow (Array U32 8#usize × U64 × Array U8 64#usize × Usize × Usize) Snapshot :=
  .cont (q.1,q.2.1,q.2.2.1,q.2.2.2,j)
theorem body (data : Slice U8) (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos i : Usize) (hp : pos.val<64)
    (hi : i.val<data.val.length) :
    PV_CBL_DigestSoft.sha_update_soft_owned_loop.body data state blocks buffer pos i =
      ok (continuing (next state blocks buffer pos data.val[i.val])
        (Usize.wrapping_add i 1#usize)) := by
  have hl : i<Slice.len data := hi
  simp only [PV_CBL_DigestSoft.sha_update_soft_owned_loop.body,if_pos hl,
    PV_CBL_ArrayStep.read data i hi,PV_CBL_ArrayMutableValue.read_write buffer pos hp,
    lift,bind_tc_ok]
  by_cases hc : Usize.wrapping_add pos 1#usize=64#usize
  · have hv : next state blocks buffer pos data.val[i.val] =
        (PV_CBL_SoftByteSource.value state (buffer.set pos data.val[i.val]),
          U64.wrapping_add blocks 1#u64,buffer.set pos data.val[i.val],0#usize) := by
      unfold next
      rw [if_pos hc]
    have hm := congrArg (fun q : Snapshot => ok (continuing q (Usize.wrapping_add i 1#usize))) hv
    refine Eq.trans ?_ hm.symm
    simp only [if_pos hc,PV_CBL_SoftByteExtracted.source,lift,bind_tc_ok,continuing]
    rfl
  · have hv : next state blocks buffer pos data.val[i.val] =
        (state,blocks,buffer.set pos data.val[i.val],Usize.wrapping_add pos 1#usize) := by
      unfold next
      rw [if_neg hc]
    have hm := congrArg (fun q : Snapshot => ok (continuing q (Usize.wrapping_add i 1#usize))) hv
    refine Eq.trans ?_ hm.symm
    simp only [if_neg hc,continuing]
    rfl
#print axioms continuing
#print axioms Snapshot
#print axioms next
#print axioms body
end R1Z.PV_CBL_DigestUpdateStep
