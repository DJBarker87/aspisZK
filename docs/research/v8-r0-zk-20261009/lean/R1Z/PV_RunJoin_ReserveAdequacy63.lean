import R1Z.PV_RunJoin_AllocatorWorld63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReserveAdequacy63
open Aeneas Aeneas.Std Result ProverRwFull
open PV_FXM_ReserveWorld PV_RunJoin_AllocatorWorld63
variable [ExternalTypes]

theorem no_growth {T S F : Type} (runtime : Runtime S F) (world : World S F)
    (v : alloc.vec.Vec T) (n : Usize)
    (room : n.val≤(runtime.metadata world v).capacity-v.val.length) :
    execute runtime world v n=⟨.ok (),PV_FXM_ReserveSelected.buffer v (runtime.metadata world v),world⟩ :=
  PV_FXM_ReserveWorld.no_growth runtime.step Usize.max (Usize.max/2) _ _ n.val world room

/-- Runtime/allocator adequacy for this request, under rdea-1. These are the
actual arithmetic guards and actual allocator outcome, not a full callback law.
This theorem does not claim the guards or allocation event witness-independent. -/
theorem growth {T S F : Type} (runtime : Runtime S F) (world : World S F)
    (v : alloc.vec.Vec T) (n : Usize)
    (width : (runtime.shape T).width≠0)
    (words : v.val.length+n.val≤Usize.max)
    (bytes : (v.val.length+n.val)*(runtime.shape T).width≤Usize.max/2)
    (address : Nat) (next : S)
    (allocation : runtime.step
      ⟨(runtime.metadata world v).address,(runtime.metadata world v).capacity,
        v.val.length+n.val,runtime.shape T⟩ world.allocator=(some address,next)) :
    (execute runtime world v n).returned=.ok () := by
  unfold execute native
  split
  · simp only [growExact,PV_FXM_ReserveSelected.buffer,width,Nat.not_lt.mpr words,Nat.not_lt.mpr bytes,ite_false]
    exact (success_capacity runtime.step (runtime.shape T)
      (PV_FXM_ReserveSelected.buffer v (runtime.metadata world v)) n.val world address next allocation).1
  · rfl

#print axioms no_growth
#print axioms growth
end R1Z.PV_RunJoin_ReserveAdequacy63
