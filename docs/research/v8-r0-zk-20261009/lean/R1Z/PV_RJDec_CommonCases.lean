import R1Z.PV_RJDec_TotalExtension
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_CommonCases
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

/-- A consumer of the six exact fixed-decoder cases. These remain native
obligations; this theorem neither selects nor alters either observer. -/
theorem complete_pair (outputs : Statement K CH → Challenges K → Aux) (adv : R1Adv K CH Aux)
    (disclosed_ok : ∀ value state, a.disclosed adv x (.ok (value,state)) =
      b.disclosed adv x (.ok (value,project state)))
    (disclosed_fail : ∀ error, a.disclosed adv x (.fail error) =
      b.disclosed adv x (.fail error))
    (disclosed_div : a.disclosed adv x .div = b.disclosed adv x .div)
    (oracle_ok : ∀ value state, a.observerOracle adv x (.ok (value,state)) =
      b.observerOracle adv x (.ok (value,project state)))
    (oracle_fail : ∀ error, a.observerOracle adv x (.fail error) =
      b.observerOracle adv x (.fail error))
    (oracle_div : a.observerOracle adv x .div = b.observerOracle adv x .div)
    (c : Coins) :
    (let v := (PV_RunJoin_Deployed.rust a).real h PrivacyR1AcctBasis.basis outputs adv x w
      (PV_RunJoin_FiniteGraph.create _ c)
     (v,(PV_RunJoin_Deployed.rust a).observe adv v)) =
    (let v := (PV_RunJoin_Deployed.rust b).real h PrivacyR1AcctBasis.basis outputs adv x w
      (PV_RunJoin_FiniteGraph.create _ c)
     (v,(PV_RunJoin_Deployed.rust b).observe adv v)) := by
  have hd := (PV_RJDec_TotalExtension.cases_iff
    (fun pair => (pair.1,project pair.2)) (a.disclosed adv x) (b.disclosed adv x)).mpr
      ⟨fun pair => disclosed_ok pair.1 pair.2,disclosed_fail,disclosed_div⟩
  have ho := (PV_RJDec_TotalExtension.cases_iff
    (fun pair => (pair.1,project pair.2)) (a.observerOracle adv x) (b.observerOracle adv x)).mpr
      ⟨fun pair => oracle_ok pair.1 pair.2,oracle_fail,oracle_div⟩
  exact PV_RunJoin_CommonObserver32.complete_pair a b project h x w
    entropy_step body_step initial outputs adv hd ho c
#print axioms complete_pair
end R1Z.PV_RJDec_CommonCases
