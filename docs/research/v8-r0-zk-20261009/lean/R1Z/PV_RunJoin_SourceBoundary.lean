import R1Z.PV_RunJoin_SourceConstructor
import R1Z.PV_RunJoin_Boundary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceBoundary
open Aeneas Aeneas.Std Result
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N C Context Rest : Type}
variable (world : PV_RunJoin_CompletedWorld.Data Coins N ProverRwRetryModel.Store C)
    (policy : ProverRwEffectCallback.Account N)
    (inputs : (h : HonestProver K) → (x : Statement K CommitHandle) → h.Instance →
      PV_RunJoin_PureSourceLift.Inputs N C)
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N ProverRwRetryModel.Store C) → View K CommitHandle Aux R1Bat)
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N ProverRwRetryModel.Store C) → List (Bytes × OracleAnswer))
    (ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat)
local notation "runtime" => PV_RunJoin_SourceConstructor.runtime world policy inputs disclosed oracle ideal
local notation "State" => PV_RunJoin_UnifiedRetry.State N ProverRwRetryModel.Store C

/-- Two operational fields installed from checked source constructions. All
other boundary data remain explicit, including the native density, actual
filesystem projection and complete observer association. -/
def boundary (d : PV_RunJoin_Boundary.Data runtime Context Rest) :
    PV_RunJoin_Boundary.Data runtime Context Rest :=
  {d with sourceBody := fun h x w => PV_RunJoin_PureSourceLift.sourceBody (inputs h x w)
          draw := ProverRwRngCaller.Tape.Insts.Prover_rw_rng_callerDraw64}

theorem source_V045 (d : PV_RunJoin_Boundary.Data runtime Context Rest)
    (h : HonestProver K) (x : Statement K CommitHandle) :
    (∀ w : h.Instance, h.public w = x.1 →
      PV_RunJoin_UnifiedRetry.BodySourceLaw
        ((boundary world policy inputs disclosed oracle ideal d).sourceBody h x w)
        ((runtime).body h x w)) ∧
    (∀ (s : State) k nonce next,
      (runtime).account.call_mut s k = .ok (nonce,next) → next.provider = s.provider) ∧
    (∀ w : h.Instance, h.public w = x.1 → ∀ secret (s next : State) status,
      (runtime).body h x w secret s = .ok (status,next) → next.provider = s.provider) := by
  refine ⟨fun w _ => PV_RunJoin_PureSourceLift.source_law (inputs h x w),?_,?_⟩
  · intro s k nonce next run
    exact PV_RunJoin_SourceAccount.provider_frame policy s next k nonce run
  · intro w _ secret s next status run
    exact PV_RunJoin_PureSourceLift.provider_frame (inputs h x w) secret s next status run

theorem native_fill_V336 (d : PV_RunJoin_Boundary.Data runtime Context Rest)
    (p : ProverRwRngCaller.Tape) (_inside : p.used.val < p.replies.val.length) :
    (boundary world policy inputs disclosed oracle ideal d).draw.fill p (Array.repeat 64#usize 0#u8) =
      ProverRwRngCaller.Tape.Insts.Prover_rw_rng_callerDraw64.fill p (Array.repeat 64#usize 0#u8) := rfl

#print axioms source_V045
#print axioms native_fill_V336
end R1Z.PV_RunJoin_SourceBoundary
