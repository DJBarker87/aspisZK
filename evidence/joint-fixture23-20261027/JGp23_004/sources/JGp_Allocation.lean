import JGn_PrepareBuffer
import JGi_TX1Ready
set_option autoImplicit false
namespace AspisR1.JGp_Allocation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- Successful allocator interpretation, using the existing owned allocation
model. No verifier child is replaced and no acceptance is assumed. -/
def filled {T : Type} (_copy : core.marker.Copy T) (n : Usize) (x : T) :
    Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) := do
  let r ← OraclePortStdAllocation.filled n x true
  match r with
  | .error _ => ok (.Err aspis_core.r0.Error.Allocation)
  | .ok v => ok (.Ok v)

def base (ops : Ops) : Ops := {ops with op1:=filled}

def buffer : alloc.vec.Vec U8 := ⟨JGn_PrepareBuffer.buffer.val,JGn_PrepareBuffer.buffer.property⟩

theorem allocated : filled core.marker.CopyU8 14759#usize 0#u8=ok (.Ok buffer) := by
  unfold filled
  rw [OraclePortStdAllocation.filled_exact]
  simp only [if_true,bind_tc_ok]
  rfl
#print axioms allocated
#print OraclePortStdAllocation.filled
end AspisR1.JGp_Allocation
