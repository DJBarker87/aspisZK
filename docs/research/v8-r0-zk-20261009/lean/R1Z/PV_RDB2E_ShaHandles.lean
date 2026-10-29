import R1Z.PV_RDB2D_SHAState
namespace R1Z.PV_RDB2E_ShaHandles
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Core := PV_DL_ShaFinal.Core
abbrev State := PV_DL_ShaFinal.State
structure Frame where
  core : Core
  buffer : Array U8 64#usize
  pos : U8
  output : Array U8 32#usize

def putState (current : Frame) (s : State) : Frame :=
  {current with core := {current.core with state:=s}}
def putBuffer (current : Frame) (b : Array U8 64#usize) : Frame :=
  {current with buffer:=b}
def putPos (current : Frame) (p : U8) : Frame := {current with pos:=p}
def putOutput (current : Frame) (o : Array U8 32#usize) : Frame :=
  {current with output:=o}
def stateHandle (before : Frame) : State × (Frame → State → Frame) :=
  (before.core.state,putState)
def bufferHandle (before : Frame) : (Array U8 64#usize) × (Frame → (Array U8 64#usize) → Frame) :=
  (before.buffer,putBuffer)
def outputHandle (before : Frame) : (Array U8 32#usize) × (Frame → (Array U8 32#usize) → Frame) :=
  (before.output,putOutput)

theorem state_handle_current (before current : Frame) (s : State) :
    (stateHandle before).2 current s=putState current s := rfl

theorem buffer_handle_current (before current : Frame) (b : Array U8 64#usize) :
    (bufferHandle before).2 current b=putBuffer current b := rfl

theorem output_handle_current (before current : Frame) (o : Array U8 32#usize) :
    (outputHandle before).2 current o=putOutput current o := rfl

theorem state_readback (current : Frame) (s : State) :
    (putState current s).core.state=s := rfl

theorem state_frame (current : Frame) (s : State) :
    (putState current s).core.block_len=current.core.block_len ∧
    (putState current s).buffer=current.buffer ∧
    (putState current s).pos=current.pos ∧
    (putState current s).output=current.output := ⟨rfl,rfl,rfl,rfl⟩

theorem state_buffer_commute (current : Frame) (s : State) (b : Array U8 64#usize) :
    putState (putBuffer current b) s=putBuffer (putState current s) b := rfl

theorem state_output_commute (current : Frame) (s : State) (o : Array U8 32#usize) :
    putState (putOutput current o) s=putOutput (putState current s) o := rfl

theorem every_state_word (current : Frame) (s : State) (i : Nat) :
    (putState current s).core.state.val[i]?=s.val[i]? := rfl

#print axioms state_handle_current
#print axioms buffer_handle_current
#print axioms output_handle_current
#print axioms state_readback
#print axioms state_frame
#print axioms state_buffer_commute
#print axioms state_output_commute
#print axioms every_state_word
end R1Z.PV_RDB2E_ShaHandles
