import R1Z.PV_RunJoin_FaultAudit
import R1Z.PV_RunJoin_Deployed
/- First-draw source proof restated under the assigned module prefix from
read-only runjoin source SHA256 20a289c9a62e837effd4bea1bfc0dec034d7045158dbabcfbfe5bc1eee7db71b.
The old OsFailure source/object is absent from the rebuilt shared tree. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_RuntimeFirstDraw
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
local notation "K" => PrivacyR1AcctBasis.K
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C : Type}
variable (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)

/-- Exact first-draw schedule, after the public account callback. It contains
no witness, body execution, model-success, bad-event, or decoder premise. -/
structure FirstDrawFailure (r : PV_RunJoin_Deployed.World runtime) where
  next : PV_RunJoin_Deployed.State N L C
  nonce : Array U8 32#usize
  after : Tape
  written : Array U8 64#usize
  error : getrandom.error.Error
  account : runtime.account.call_mut r.state (ProverCommitRetrySource34.word 0) = .ok (nonce,next)
  entered : entropy_nonzero32 nonce = .ok true
  reply : Tape.Insts.Prover_rw_rng_callerDraw64.fill next.provider (Array.repeat 64#usize 0#u8) =
    .ok ((after,.Err error),written)

theorem execute_failure (r : PV_RunJoin_Deployed.World runtime)
    (fault : FirstDrawFailure runtime r) (h : HonestProver K)
    (x : Statement K CommitHandle) (w : h.Instance) :
    PV_RunJoin_Deployed.execute runtime h x w r =
      .ok (.stop .Entropy,{fault.next with provider := fault.after}) :=
  PV_RunJoin_FaultAudit.client_os_error runtime.account (runtime.body h x w)
    r.state fault.next fault.nonce fault.after fault.account fault.entered
    fault.written fault.error fault.reply


#print axioms execute_failure
end R1Z.PV_OptB_RuntimeFirstDraw
