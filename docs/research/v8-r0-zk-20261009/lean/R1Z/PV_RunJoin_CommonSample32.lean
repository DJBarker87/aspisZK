import R1Z.PV_RunJoin_AttemptProjection32
import R1Z.PV_RunJoin_Deployed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonSample32
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

/-- The same completion sample feeds both actual retry interpreters. This is
 a compositional source theorem; no native source/decoder law is installed. -/
theorem execute (c : Coins) :
    mapR (fun out => (out.1,project out.2))
      (PV_RunJoin_Deployed.execute a h x w (PV_RunJoin_FiniteGraph.create _ c)) =
    PV_RunJoin_Deployed.execute b h x w (PV_RunJoin_FiniteGraph.create _ c) := by
  change mapR _ (client a.account (a.body h x w) (PV_RunJoin_Deployed.initialState a c)) =
    client b.account (b.body h x w) (PV_RunJoin_Deployed.initialState b c)
  rw [← initial c]
  exact PV_RunJoin_AttemptProjection32.client project a.account b.account
    (a.body h x w) (b.body h x w) entropy_step body_step _
#print axioms execute

/-- Complete ROMView, including the observer oracle stream, follows from
 per-step simulations and the two explicit decoder laws. These laws remain
 P work for a deployed instance; no equality is added to TrustItems. -/
theorem complete_view (outputs : Statement K CH → Challenges K → Aux) (adv : R1Adv K CH Aux)
    (disclosed : ∀ out, a.disclosed adv x out =
      b.disclosed adv x (mapR (fun pair => (pair.1,project pair.2)) out))
    (oracle : ∀ out, a.observerOracle adv x out =
      b.observerOracle adv x (mapR (fun pair => (pair.1,project pair.2)) out))
    (c : Coins) :
    (PV_RunJoin_Deployed.rust a).real h PrivacyR1AcctBasis.basis outputs adv x w
      (PV_RunJoin_FiniteGraph.create _ c) =
    (PV_RunJoin_Deployed.rust b).real h PrivacyR1AcctBasis.basis outputs adv x w
      (PV_RunJoin_FiniteGraph.create _ c) := by
  have he := execute a b project h x w entropy_step body_step initial c
  change ⟨a.disclosed adv x _,a.observerOracle adv x _⟩ =
    (⟨b.disclosed adv x _,b.observerOracle adv x _⟩ : ROMView K CH Aux R1Bat)
  rw [disclosed,oracle,he]
#print axioms complete_view
end R1Z.PV_RunJoin_CommonSample32
