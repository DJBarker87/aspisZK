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

## Stage 3 — candidate step and arbitrary owned prefixes

The new Kani `state_only_hiding::material15::candidate_step` checks one
literal iteration body of shipped `SeedExpander::m31` against the owned
`try_step`, with arbitrary seed, wrapping counter, buffered bytes and any
legal initial word 0–8. It uses the previously accepted verified next-word
contract; the reference transition is executed. It does not use a scalar
summary stub or constrain the first acceptance index. No vector occurs in
this check. Both candidate acceptance and rejection are included.

`candidate-step-v1` passes: exit 0, wall **15.104 s**, peak RSS **671648 KiB**,
zero swaps. All 1795 checks pass with unwinding assertions. Time is spent in
Kani compilation and one bounded transition verification, not arithmetic
elimination. The proof-only source derives from part 14's immutable host
snapshot, plus the appended `material15` harness; its production prefix
remains byte-identical to `542fe958f`. The inherited proof-only callee
annotations and local ROM trust boundary are reused. Receipt revision is
the research base; exact proof-input source hashes distinguish the harness.
The host proof binary is recorded by SHA256 and size in `kani-artifacts.json`;
no binary is committed. `#print axioms` is N/A for Kani.

`R1Z.ProverCommitMaterialPrefix` proves `arbitrary_prefix` for a generic
owned vector accumulator with any scalar result/state transition and any
vector element type. Its capacity premise is explicit:
`values.val.length + n ≤ Usize.max`. Errors preserve their final state;
unpublished partial vector contents are erased. The successful result is
exactly the original prefix followed by the collected suffix. `prepend_assoc`
is proved by induction over the existing prefix; `m31_prefix` and
`qm31_prefix` specialize the generic accumulator to the material scalar and
tower callers. No numeric prefix-length restriction is imposed.

**Boundary:** these are generic accumulator specializations. They do not
assert equality with the extracted material collectors or instantiate a
shipped mutable-source vector loop. The attempted direct accumulator
identifications fail in J8397 and J8398 despite printing superficially
identical monadic expressions. Both diagnostics, including generated
`sorryAx`, are excluded. The final source removes those attempted bridges;
it does not assume or rename them into source-refinement certificates.
The accepted per-candidate law and generic prefix lemmas therefore constitute
separate components, not the requested universal source-cell P6 theorem.
Part 14's nine bounded M31 source-cell checks and earlier four-call QM31
control-flow checks remain valid within their original domains; they are
reused without an unchanged rerun.

## Final cached Lean audit

The smallest changed generic module was checked first (J8397, J8398), with
the failed bridges excluded as above. The final **J8399** compiles the adopted
`R1Z.ProverCommitMaterialPrefix` against the prior `ProverCommit14Audit` and
the new fixed endpoint, and prints all prior 33 and all new 7 axiom audits.
It is the single final cached dependency audit for this addition, not a
package-wide rebuild or a shipped-runtime release certificate.

Exact target: `R1Z/ProverCommitMaterialPrefix.lean`; exit **0**;
wall **2.07 s**; peak RSS **4153408 KiB**; swaps **0**;
source revision **`0a1cb4d79`** plus the exact additive source SHA retained in
`lean/sources/attempt-8399-ProverCommitMaterialPrefix.lean.txt` and the JSONL
receipt. All **40** `#print axioms` lines contain only subsets of
`[propext, Classical.choice, Quot.sound]`. Cgroup limits remain
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
No unchanged full regression is repeated.

## Demonstrated limits and next deliverable

1. **Source-prefix and QM31 transport remains open.** The universal owned
   accumulator lemmas have no accepted bridge to the actual mutable source
   loop. The previously recorded Aeneas borrowed-loop context-join failure
   is not rerun unchanged. Fixing that extraction or proving an explicit
   source iteration/context refinement is required before claiming arbitrary
   source-prefix or whole-column transport.
2. **Returned-material assembly remains open.** The source consumes the
   nonce store, derives a seed, builds c1 and every mask-only column, builds
   and balances g, fills and balances h1 padding, and then moves those fields
   into `StateOnlyMaskMaterial` (`state_only_hiding.rs:438–489`). The new
   generic lemmas do not cover those callers, balancing integration, nonce
   reservation, allocator semantics or returned-object disposal.
3. **The actual builder/checker/retry history remains open.** The current
   endpoint's `source` is the constructed `fsR1P`, not an independently
   represented Rust execution. `ModelExecutionJoin` contains equality of
   rational Boolean tests, not equality of histories. The fixed observer
   removes the previous observer counterexample but cannot manufacture the
   missing source execution carrier and its refinement. In addition,
   `GamesR1PBin.realOut` evaluates `runC` over the full N-attempt carrier,
   whereas `prove_masked_retrying_with` returns immediately on the first
   success or non-rejection error. D52.3 explicitly calls this conservative.
   A stopped-prefix/shared-table transport is needed; this is not reported
   as a counterexample to public-view equivalence or model privacy.
4. **All-family shared-oracle coverage remains open.** Neither the local
   candidate ROM nor the vector-prefix algebra instantiates the complete
   seed, packing, D, salt, tree, verifier, retry and abort callback sequence.
   The part-14 callback obligation ledger is reused, not marked discharged.

The literal deletion removes both named *model* joins in the new endpoint.
It does **not** close the shipped obligations formerly described by their
names. The unqualified old `privacy_headline_admitted` remains unchanged.
No production source, frozen ELF, public game, query budget, bad event,
security target, or numerical error term is changed. The actual shipped
privacy target is **not yet established**.

The assigned Env J range is exhausted at **8399**, including the retained
failed diagnostics. No attempt 8400 or another worker's number is used.
Further Lean development needs another allocated range; the next concrete
proof is the explicit material-collector/accumulator bridge, followed by the
actual source context refinement and returned assembly. No unchecked bridge
or failed diagnostic is adopted merely because the allocation ended.
