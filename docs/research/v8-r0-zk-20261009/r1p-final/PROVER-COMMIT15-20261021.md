# Prover commitment part 15 — fixed observer and source transport

Base: `542fe958f`; branch `codex/cx-prover-commit15-20261021`.
No production source, peer-owned proof file, wallet, key, or frozen artifact is modified.

## Scope and statement audit

The part-14 counterexample concerns unrestricted replacement observer programs.
The new endpoint explicitly specializes to `fun adv => adv.prog` of the
constructed `fsR1P` source. Both sides of the old endpoint are literally that
same model. Identity joins at this endpoint must not be described as shipped
Rust execution refinement. The actual source integration remains a separate
obligation, even if the named model premises can be deleted.

## Stage 1 — fixed observer

Work in progress. Exact statements, deletion evidence and host receipts follow.

The explicit specialization is `R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted`
in `R1Z/ProverCommitFixedEndpoint.lean`. `observer_program` is fixed to the
constructed source adversary's own `R1Adv.prog`. All adversaries and their
decision functions remain quantified. No query budget, failure event,
randomness carrier, conclusion or numerical bound changes.

J8391 compiles `ProverCommitFixedObserver`: exit 0, 1.55 s, peak RSS
3508116 KiB, zero swaps. J8395 compiles the explicit specialization with
both old join binders retained but unused: exit 0, 6.63 s, peak RSS
4176568 KiB, zero swaps. All accepted printed axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Base revision is `542fe958f`;
exact new source snapshots, SHA256, transitive object fingerprints,
commands/errors/timing/axioms are in the part-15 `lean/` receipts.
J8390 is an excluded missing-instance diagnostic; J8392–8393 are excluded
notation precheck errors; J8394 is an excluded tactic-transparency failure.
No failed generated `sorryAx` diagnostic is adopted. J8395 removes the
unnecessary rewrite tactic: structure eta equality supplies identity directly.

The host launcher uses existing slot locks until 17:00 London, per the lead,
and exactly 6G/8G/no-swap/64-task scopes. No host dependency cache is rebuilt.
The new endpoint is a new file; no imported shared source/object is replaced.

## Stage 2 — deletion at the explicit specialization

Both named model premises, `R_wire_builder_checker_D75_retry` and
`G_sim_R_wire`, are removed from the new specialized endpoint. No premise
is added or repackaged; the old unrestricted endpoint is preserved.
J8396: exit 0, wall 6.79 s, peak RSS 4170756 KiB, swaps 0; source revision
`4a030bd31`, exact SHA and dependency fingerprint in the receipt. Its top
theorem prints only `[propext, Classical.choice, Quot.sound]`.

The specialization's before text places the result colon on its own line
(a whitespace-only normalization of J8395) so the reviewed subsequent diff
is literally deletion-only. The compiled J8395 bytes are separately retained
in `lean/sources/attempt-8395-ProverCommitFixedEndpoint.lean.txt`.
`headline-deletions.diff` has no added source line.

**This establishes model privacy, not shipped-Rust privacy.** The `source`
notation in both endpoints is `fsR1P` of the owned decoder and canonical
builder. Its randomness carriers contain model tables/coins, not source
machine executions. `ModelExecutionJoin` compares rational Boolean tests,
not histories. Identifying that constructed model with the shipped runtime
is neither a binder of this endpoint nor a consequence of identity.
The shipped target remains **not yet established**.

Before specialization-premise deletion (verbatim):

```lean
import R1Z.ProverCommitAdmittedEndpoint
import R1Z.ProverCommitFixedObserver
/-! Explicit canonical admitted-domain specialization of the owned headline.
This fixes the mathematical builder, not its outstanding shipped Rust identification. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver
abbrev ownedDecode := ProverCommitOwnedDecoder.decoder (K := PrivacyR1AcctBasis.K)
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)

local notation "log" => PhaseWireLog2Bin.log
local notation "base" => PrivacyR1AcctModel.base template log
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def input : HonestProver K := BuilderSource.prover

variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

local notation "fib" => PhaseWireLog2Bin.fib
local notation "opens" => PhaseWireLog2Bin.opens
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
open R1Z.PrivacyR1HeadlineWire2
local notation "source" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
local notation "observer_program" => (fun (adv : R1Adv K CommitHandle Aux) => R1Adv.prog adv)

theorem privacy_headline_admitted
    (R_wire_builder_checker_D75_retry : ∀ (adv : (source).Adversary) (w : (R0Z.ZkStatement.HonestProver.Instance h)),
      (R0Z.ZkStatement.HonestProver.public h w) = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos
          (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : (source).Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x))
      (idealTestS (fsR1P (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) 8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)) (QueryScanIdealHistory.selectedBad))
 :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  exact PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed template input outputs x
    (Admitted.builder_premises (x := x)) observer_program
    (by
      intro adv w hw
      exact ProverCommitFixedObserver.self_join _ _)
    (by
      intro adv
      exact ProverCommitFixedObserver.self_join _ _)

#print axioms privacy_headline_admitted
end R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver
```

After (verbatim):

```lean
import R1Z.ProverCommitAdmittedEndpoint
import R1Z.ProverCommitFixedObserver
/-! Explicit canonical admitted-domain specialization of the owned headline.
This fixes the mathematical builder, not its outstanding shipped Rust identification. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver
abbrev ownedDecode := ProverCommitOwnedDecoder.decoder (K := PrivacyR1AcctBasis.K)
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)

local notation "log" => PhaseWireLog2Bin.log
local notation "base" => PrivacyR1AcctModel.base template log
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def input : HonestProver K := BuilderSource.prover

variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

local notation "fib" => PhaseWireLog2Bin.fib
local notation "opens" => PhaseWireLog2Bin.opens
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
open R1Z.PrivacyR1HeadlineWire2
local notation "source" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
local notation "observer_program" => (fun (adv : R1Adv K CommitHandle Aux) => R1Adv.prog adv)

theorem privacy_headline_admitted
 :
    ZK_FSS h B outputs source x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  exact PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed template input outputs x
    (Admitted.builder_premises (x := x)) observer_program
    (by
      intro adv w hw
      exact ProverCommitFixedObserver.self_join _ _)
    (by
      intro adv
      exact ProverCommitFixedObserver.self_join _ _)

#print axioms privacy_headline_admitted
end R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver
```
