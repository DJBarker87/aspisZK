import R1Z.PV_RunJoin_CommonSample32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonObserver32
open Aeneas Aeneas.Std Result R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
open PV_RunJoin_UnifiedRetry ProverCommitSemanticTransport26
local notation "K" => PrivacyR1AcctBasis.K
variable [ProverRwFull.ExternalTypes]
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {CH Aux Coins NA LA CA NB LB CB : Type}
variable (a : PV_RunJoin_Deployed.Runtime CH Aux Coins NA LA CA)
    (b : PV_RunJoin_Deployed.Runtime CH Aux Coins NB LB CB)
    (project : State NA LA CA → State NB LB CB)
    (h : R0Z.ZkStatement.HonestProver K) (x : Statement K CH) (w : h.Instance)
    (entropy_step : ∀ index s,
      mapR (fun out => (out.1,project out.2)) (entropy a.account index s) = entropy b.account index (project s))
    (body_step : ∀ secret s,
      mapR (fun out => (out.1,project out.2)) (a.body h x w secret s) = b.body h x w secret (project s))
    (initial : ∀ c, project (PV_RunJoin_Deployed.initialState a c)=PV_RunJoin_Deployed.initialState b c)
include entropy_step body_step initial

/-- Both components of RustRealRefinement's observable pair at the same
completion sample. No observer event or result class is projected away. The
step/decoder laws are explicit source obligations, not extraction trust. -/
theorem complete_pair (outputs : Statement K CH → Challenges K → Aux) (adv : R1Adv K CH Aux)
    (disclosed : ∀ out, a.disclosed adv x out =
      b.disclosed adv x (mapR (fun pair => (pair.1,project pair.2)) out))
    (oracle : ∀ out, a.observerOracle adv x out =
      b.observerOracle adv x (mapR (fun pair => (pair.1,project pair.2)) out))
    (c : Coins) :
    (let v := (PV_RunJoin_Deployed.rust a).real h PrivacyR1AcctBasis.basis outputs adv x w
      (PV_RunJoin_FiniteGraph.create _ c)
     (v,(PV_RunJoin_Deployed.rust a).observe adv v)) =
    (let v := (PV_RunJoin_Deployed.rust b).real h PrivacyR1AcctBasis.basis outputs adv x w
      (PV_RunJoin_FiniteGraph.create _ c)
     (v,(PV_RunJoin_Deployed.rust b).observe adv v)) := by
  have hv := PV_RunJoin_CommonSample32.complete_view a b project h x w
    entropy_step body_step initial outputs adv disclosed oracle c
  exact congrArg (fun v => (v,adv.decide v)) hv
#print axioms complete_pair
end R1Z.PV_RunJoin_CommonObserver32
