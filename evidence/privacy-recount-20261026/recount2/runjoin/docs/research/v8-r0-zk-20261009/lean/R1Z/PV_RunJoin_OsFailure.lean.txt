import R1Z.PV_RunJoin_FaultAudit
import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OsFailure
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

/-- Equality of the entire returned state and complete view, for ANY two
bodies/witnesses at the same public input, on the named schedule. -/
theorem witness_independent (r : PV_RunJoin_Deployed.World runtime)
    (fault : FirstDrawFailure runtime r) (h : HonestProver K)
    (x : Statement K CommitHandle) (w u : h.Instance)
    (adv : R1Adv K CommitHandle Aux)
    (B : PackBasis PrivacyR1AcctBasis.F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) :
    PV_RunJoin_Deployed.execute runtime h x w r = PV_RunJoin_Deployed.execute runtime h x u r ∧
    (PV_RunJoin_Deployed.rust runtime).real h B outputs adv x w r =
      (PV_RunJoin_Deployed.rust runtime).real h B outputs adv x u r := by
  have left := execute_failure runtime r fault h x w
  have right := execute_failure runtime r fault h x u
  refine ⟨left.trans right.symm,?_⟩
  change (⟨_,_⟩ : ROMView K CommitHandle Aux R1Z.Batched.R1Bat) = ⟨_,_⟩
  rw [left,right]

/-- The unchanged bad predicate contains exactly these three coordinate
conditions; OS status is not a fourth disjunct. This proves a conditional
outside-bad fact, not existence of a concrete successful source coin. -/
theorem outside_bad_iff {M : Type} (old : Fin 8 → M → Prop)
    (queries : M → List ProverCommitSeedEvent19.Entry)
    (r : (M × OracleAnswer) × ProverCommitFuelJoin22.Tape) :
    (¬ ∃ i, ProverCommitFuelJoin22.bad old queries i r) ↔
      (∀ i, ¬ old i r.1.1) ∧
      ¬ ProverCommitSeedEvent19.seedGuess (queries r.1.1) r.1.2 ∧
      (∀ j, ¬ ProverCommitFuelJoin22.failure j r.2) := by
  simp only [ProverCommitFuelJoin22.bad,ProverCommitSeedEvent19.augmented]
  constructor
  · intro hn
    refine ⟨fun i hi => hn ⟨i,Or.inl (Or.inl hi)⟩,
      fun hs => hn ⟨0,Or.inl (Or.inr ⟨rfl,hs⟩)⟩,
      fun j hj => hn ⟨0,Or.inr ⟨rfl,j,hj⟩⟩⟩
  · rintro ⟨ho,hs,hf⟩ ⟨i,(hi | ⟨_,hi⟩) | ⟨_,j,hj⟩⟩
    · exact ho i hi
    · exact hs hi
    · exact hf j hj

/-- Exact conditional view disagreement. Native error decoding and model
success are explicit obligations: this theorem does not manufacture them
from the free Runtime record. The preceding theorem supplies the exact
coordinate test for its unchanged outside-bad premise. -/
theorem conditional_disagreement (r : PV_RunJoin_Deployed.World runtime)
    (fault : FirstDrawFailure runtime r) (h : HonestProver K)
    (x : Statement K CommitHandle) (w : h.Instance)
    (adv : R1Adv K CommitHandle Aux) (B : PackBasis PrivacyR1AcctBasis.F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (model : ROMView K CommitHandle Aux R1Z.Batched.R1Bat)
    (decoded : runtime.observerOracle adv x
      (.ok (.stop .Entropy,{fault.next with provider := fault.after})) = [])
    (success : model.observerOracle ≠ []) :
    (PV_RunJoin_Deployed.rust runtime).real h B outputs adv x w r ≠ model := by
  intro same
  have logs := congrArg ROMView.observerOracle same
  change runtime.observerOracle adv x (PV_RunJoin_Deployed.execute runtime h x w r) = _ at logs
  rw [execute_failure runtime r fault h x w,decoded] at logs
  exact success logs.symm

#print axioms execute_failure
#print axioms witness_independent
#print axioms outside_bad_iff
#print axioms conditional_disagreement
end R1Z.PV_RunJoin_OsFailure
