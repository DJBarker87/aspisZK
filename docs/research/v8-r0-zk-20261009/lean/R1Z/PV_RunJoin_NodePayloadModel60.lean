import R1Z.PV_RunJoin_NodeTailModel60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NodePayloadModel60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54
abbrev Payload := Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)

def model (payload : Payload) (cap : Nat) : ProverCommitPublish43.Slot :=
  ⟨match payload with | .ok (.Ok nodes) => .ok (bytes nodes.val) | _ => .error .merkle,cap⟩

def run (out : alloc.vec.Vec U8) (payload : Payload) (cap : Usize) : Payload := do
  let r ← payload
  match r with
  | .Err e => ok (.Err e)
  | .Ok nodes => do
    let next ← PV_RunJoin_NodeTail41.finish out nodes cap
    ok (.Ok next)

theorem complete (out : alloc.vec.Vec U8) (payload : Payload) (cap : Usize)
    (room : out.length+2*cap.val≤Usize.max) :
    resultBytes (run out payload cap)=
      exceptBytes (ProverCommitPublish43.appendSlot (bytes out.val) (model payload cap.val)) := by
  cases payload with
  | fail e => rfl
  | div => rfl
  | ok status =>
    cases status with
    | Err e => rfl
    | Ok nodes => exact PV_RunJoin_NodeTailModel60.complete out nodes cap room

#print axioms complete
end R1Z.PV_RunJoin_NodePayloadModel60
