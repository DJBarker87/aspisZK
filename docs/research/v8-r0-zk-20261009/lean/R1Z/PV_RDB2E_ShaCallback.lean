import R1Z.PV_RDB2E_ShaHandles
namespace R1Z.PV_RDB2E_ShaHandles
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def callback (compress : State → List U8 → Result State) (current : Frame)
    (block : List U8) : Result Frame := do
  let (state,back) := stateHandle current
  let after ← compress state block
  ok (back current after)

def callbackRun (compress : State → List U8 → Result State) :
    List (List U8) → Frame → Result Frame
  | [],current => ok current
  | block::tail,current => do
    let after ← callback compress current block
    callbackRun compress tail after

theorem callback_source (compress : State → List U8 → Result State) (current : Frame)
    (block : List U8) :
    callback compress current block=(do let s ← compress current.core.state block; ok (putState current s)) := rfl

theorem put_state_twice (current : Frame) (first last : State) :
    putState (putState current first) last=putState current last := rfl

theorem callback_run (compress : State → List U8 → Result State)
    (blocks : List (List U8)) (current : Frame) :
    callbackRun compress blocks current=
      (do let s ← PV_DL_CompressionTrace.run compress blocks current.core.state
          ok (putState current s)) := by
  induction blocks generalizing current with
  | nil => rfl
  | cons block tail ih =>
    simp only [callbackRun,callback_source,PV_DL_CompressionTrace.run,bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro s hs
    rw [ih]
    rfl

theorem callback_failure (compress : State → List U8 → Result State) (current : Frame)
    (block : List U8) (e : Error) (fails : compress current.core.state block=fail e) :
    callback compress current block=fail e := by
  simp only [callback_source,fails,bind_tc_fail]

#print axioms callback_source
#print axioms put_state_twice
#print axioms callback_run
#print axioms callback_failure
end R1Z.PV_RDB2E_ShaHandles
