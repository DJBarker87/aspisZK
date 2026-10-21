# Prover commitment part 16 — deployed boundary and ordered queries

Base `d9c3ed7ab`; branch `codex/cx-prover-commit16-20261021`.
No production source or concurrent-worker module is changed.

## Stage 1 — initial explicit deployed premise (J8609)

`PrivacyR1HeadlineDeployed.privacy_headline_deployed` quantifies an independent
`rust : FSExperiments`, its finite randomness carriers and its observer program.
Its sole proof premise is `RustProverRefinement`. It compares whole public
`ROMView` values (including ordered observer history) and decisions, on
couplings, outside the exact existing realBad/selectedBad. It does not assert
an internal-machine-state or proof-byte representation absent from FSExperiments.
A concrete runtime adapter still has to prove that its experiment models every
builder, checker, retry, serialisation, abort and shared-oracle operation.
This is a named open source obligation, not a cryptographic assumption or a
concrete shipped instance. The premise cannot disappear by fixing the model's
observer: the conclusion concerns the independent runtime experiment.

The model-level fixed `privacy_headline_admitted` supplies its exact numerical
ledger. The general `privacy_R1_protocol_caller` transports the runtime through
the projected joins, charging the fixed exceptions once; an extra triangle
inequality against an already charged model theorem would double-charge them.
The complete old error expression and < 2^-100 conclusion are retained.
This packages an obligation; it does not discharge RustProverRefinement.

Focused J8608 failed on notation field syntax and is excluded. Changed-source
J8609 passed: exit 0, wall 8.03s, peak RSS 4190664 KiB, swaps 0, source revision
`d9c3ed7ab` plus the exact source snapshot hash in the receipt. Both axiom
audits contain only `[propext, Classical.choice, Quot.sound]`. All jobs use
6G/8G/no-swap/TasksMax64 scopes and existing launcher slot locks. J8600–8607
were already present and skipped. No dependency object was rebuilt.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit16-20261021/lean/`.

Verbatim initial source (superseded by the ordered deployed endpoint below):

```lean
import R1Z.ProverCommitFixedEndpoint
import R1Z.ProverCommitFixedObserver
/-! Explicit canonical admitted-domain specialization of the owned headline.
This fixes the mathematical builder, not its outstanding shipped Rust identification. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineDeployed
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
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)

/-- Equality of the full observable execution and the observer's decision,
not merely equality of acceptance or a hash. The independently supplied
runtime must include builder/checker/retry, ordered wire and oracle history
in its FS experiment. No concrete Rust instance is supplied here. -/
structure WholeRunJoin {R M : Type} [Fintype R] [Fintype M]
    (runtime : R → ROMView K CommitHandle Aux R1Bat × Bool)
    (model : M → ROMView K CommitHandle Aux R1Bat × Bool)
    (bad : Fin 8 → M → Prop) where
  cp : Coupling R M
  agreement : ∀ s, ¬ (∃ i, bad i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s)

def WholeRunJoin.tests {R M : Type} [Fintype R] [Fintype M]
    {runtime : R → ROMView K CommitHandle Aux R1Bat × Bool}
    {model : M → ROMView K CommitHandle Aux R1Bat × Bool}
    {bad : Fin 8 → M → Prop} (join : WholeRunJoin runtime model bad) :
    ModelExecutionJoin (fun r => bit (runtime r).2) (fun m => bit (model m).2) bad where
  cp := join.cp
  agreement := fun s hn => congrArg (fun run => bit run.2) (join.agreement s hn)

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

/-- The explicit deployed obligation. Both sides include the complete public
view, ordered observer history and observer decision. The exceptions are the
existing realBad/selectedBad, not predicates chosen by the implementation. -/
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (WholeRunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w))) ∧
  (∀ adv : rust.Adversary, Nonempty (WholeRunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  have model := PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted
    template outputs x
  constructor
  · intro adv w hw
    obtain ⟨hpub, hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
    have caller := ProverCommitOwnedEndpoint.caller_law template input outputs x
    apply (PrivacyR1FinalProtocolCaller.privacy_R1_protocol_caller
      base h B outputs x seed hB hpub hs caller coins
      (PhaseWireLog2Bin.batches input outputs x template decode)
      (PhaseWireLog2Bin.ordered_log input outputs x template decode)
      rust observer_program
      (fun adv w hw => (Classical.choice (refinement.1 adv w hw)).tests)
      (fun adv => (Classical.choice (refinement.2 adv)).tests)).1 adv w hw
  · exact model.2

#print axioms WholeRunJoin.tests
#print axioms privacy_headline_deployed
end R1Z.PrivacyR1HeadlineDeployed
```

## Stage 2 — ordered wire encoding

The actual current `compact::SPLIT` is 10. SER-JOIN's historical
11+11 prose and witness do not describe this source constant.


The new `PhaseWireOrdered16.OrderedChallenges` retains the full ordered,
distinct q22 and proves that its projection is the algebra's query Finset.
`batchQueries` splits at ten before normalization; `indices` sorts and
deduplicates each tree's projected batch. `batches` and `ordered_log` prove
the analogous D80 laws over this extended carrier, with the existing leaf
encoding and grammar. `simulator_schedule` proves identical public transcripts
produce identical schedules. `public_postprocessing` retains an arbitrary ε
exactly for deterministic functions of a **joint** private/public transcript.
It does not infer joint privacy from marginal privacy.

**Integration obstruction, not a complete replacement headline:**
`R0Z.HonestView.Challenges` has only a Finset; `R1Wire.comLog` and
`R1ProverP.openList` take that carrier. `no_legacy_factorization` proves for
SPLIT=10 that no such set-only function recovers the batch on every valid
ordered q22. Consequently `OrderedWireBatches` is explicitly a new interface,
not a renamed inhabitant of old `RWireBatches`. The new log's `toList` read
order remains logical; it is not certified equal to the actual verifier's
per-tree multiproof traversal. Its sorted per-tree `indices` are separate.
No equality to `dV_frozen2` is asserted. A repaired full privacy experiment
must retain query order at `dec`/`chOf`, carry it through retry and ideal
execution, and change the batch consumer accordingly. The generic
postprocessing proof shows this adds no error *once joint transcript transport
is supplied*; it does not establish that missing transport for the old
set-only endpoint. At this stage the complete ordered headline was still open; the subsequent public reencoding model below preserves its error bound. Concrete source alignment remains open.

J8610 failed on missing namespace and a reserved binder name; excluded.
Changed J8611 passed all thirteen axiom audits with standard axioms only:
exit 0, wall 2.67s, peak RSS 4159364 KiB, swaps 0, revision `b4dfa41f2`
plus the exact source hash in its receipt. No old shared module/object changed.

Verbatim source of the new interface and all adopted statements:

```lean
import R1Z.PhaseWireLog2Bin
import R1Z.SerJoinOrderObstruction
import R0Z.LawTransport
/-! Order-preserving source-facing challenge carrier. No change to the legacy
set-only Challenges or assertion of a Rust instance is made here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseWireOrdered16
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort
  R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.EventsR1PBin R1Z.CouplingR1PBin R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis

/-- Projection to the old algebra retains the exact query set; source-facing
operations retain all twenty-two ordinal positions. -/
structure OrderedChallenges where
  algebra : Challenges K
  q22 : List Fib
  length_q22 : q22.length = 22
  distinct_q22 : q22.Nodup
  query_set : q22.toFinset = algebra.queries

def batchQueries (ch : OrderedChallenges) (b : Fin 2) : Finset Fib :=
  (if b.val = 0 then ch.q22.take 10 else ch.q22.drop 10).toFinset

def batchFib (ch : OrderedChallenges) (b : Fin 2) : Fin 3 → Finset Fib :=
  PhaseWireLog2Bin.treeFib (batchQueries ch b)

def fib (ch : OrderedChallenges) : Fin 3 → Finset Fib :=
  PhaseWireLog2Bin.fib ch.algebra

/-- Sorted and deduplicated per-tree indices, after the ordered 10+12 split.
The folded mapping can identify queries within one batch. -/
def indices (ch : OrderedChallenges) (b : Fin 2) (T : Fin 3) : List Fib :=
  (batchFib ch b T).sort (· ≤ ·)

def reads (ch : OrderedChallenges) (b : Fin 2) : List (Fin 3 ⊕ RIdx) :=
  (EventsR1PBin.batchReadSet (batchFib ch b)).toList

def opens (ch : OrderedChallenges) : List (Fin 3 ⊕ RIdx) :=
  reads ch 0 ++ reads ch 1

theorem batch_lengths (ch : OrderedChallenges) :
    (ch.q22.take 10).length = 10 ∧ (ch.q22.drop 10).length = 12 := by
  simp only [List.length_take, List.length_drop, ch.length_q22]
  decide

theorem query_union (ch : OrderedChallenges) :
    batchQueries ch 0 ∪ batchQueries ch 1 = ch.algebra.queries := by
  unfold batchQueries
  simp only [Fin.val_zero, Fin.val_one, ite_true, if_neg (by decide : ¬ (1 = 0))]
  rw [← List.toFinset_append, List.take_append_drop, ch.query_set]

theorem fibre_union (ch : OrderedChallenges) (T : Fin 3) :
    fib ch T = batchFib ch 0 T ∪ batchFib ch 1 T := by
  unfold fib PhaseWireLog2Bin.fib batchFib PhaseWireLog2Bin.treeFib
  split
  · rw [← Finset.image_union, query_union]
  · exact (query_union ch).symm

theorem indices_set (ch : OrderedChallenges) (b : Fin 2) (T : Fin 3) :
    (indices ch b T).toFinset = batchFib ch b T := by
  exact Finset.sort_toFinset _ _

theorem reads_nodup (ch : OrderedChallenges) (b : Fin 2) : (reads ch b).Nodup :=
  Finset.nodup_toList _

theorem reads_coverage (ch : OrderedChallenges) (b : Fin 2) (c : Fin 3 ⊕ RIdx) :
    c ∈ reads ch b ↔ openedQ (batchFib ch b) c := by
  simp only [reads, Finset.mem_toList, EventsR1PBin.mem_batchReadSet]

theorem opens_coverage (ch : OrderedChallenges) (c : Fin 3 ⊕ RIdx) :
    c ∈ opens ch ↔ openedQ (fib ch) c := by
  rw [opens, List.mem_append, reads_coverage, reads_coverage]
  have he : fib ch = fun T => batchFib ch 0 T ∪ batchFib ch 1 T :=
    funext (fibre_union ch)
  rw [he, PhaseWireLog2Bin.opened_union]

/-- D80 batch laws at the extended carrier. This cannot inhabit the legacy
RWireBatches until that interface receives the ordered challenge. -/
structure OrderedWireBatches where
  batchFib : OrderedChallenges → Fin 2 → Fin 3 → Finset Fib
  reads : OrderedChallenges → Fin 2 → List (Fin 3 ⊕ RIdx)
  concatenation : ∀ ch, opens ch = reads ch 0 ++ reads ch 1
  nodup : ∀ ch b, (reads ch b).Nodup
  coverage : ∀ ch b c, c ∈ reads ch b ↔ openedQ (batchFib ch b) c
  fibre_union : ∀ ch T, fib ch T = batchFib ch 0 T ∪ batchFib ch 1 T

def batches : OrderedWireBatches where
  batchFib := batchFib
  reads := reads
  concatenation := fun _ => rfl
  nodup := reads_nodup
  coverage := reads_coverage
  fibre_union := fibre_union

variable {CommitHandle Aux : Type}

def log (rest : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (ch : OrderedChallenges) :
    List (List UInt8 × OracleAnswer) :=
  (opens ch).map (PhaseWireLog2Bin.entry rest roots v)

theorem ordered_log (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : (PhaseWireLog2Bin.honest h).Instance)
    (sec : SecP) (d : OracleAnswer) (τ : Tape K F)
    (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer)
    (ch : OrderedChallenges) :
    log rest roots (view (PhaseWireLog2Bin.honest h) B outputs x w ch.algebra τ) ch =
    (opens ch).map (fun c =>
      (gram [] 0 (PhaseLeafConstructionBin.leafVal PhaseLeafEncodingBin.encoding B
        (PhaseWireLog2Bin.honest h) w x τ ch.algebra) sec d rest
        (cposOf (E₁ := PrivacyR1AcctModel.E₁) (E₂ := PrivacyR1AcctModel.E₂) c),
        ansC roots rest c)) := by
  apply List.map_congr_left
  intro c hc
  exact PhaseWireLog2Bin.entry_grammar h outputs x w τ ch.algebra [] 0 sec d roots rest c
    ((opens_coverage ch c).mp hc)

/-- The simulator applies the identical public function to the retained
transcript. No witness or mask tape is an input to the batch schedule. -/
def publicSchedule {Transcript : Type} (decode : Transcript → OrderedChallenges)
    (transcript : Transcript) : List (Fin 3 ⊕ RIdx) := opens (decode transcript)

theorem simulator_schedule {Transcript : Type} (decode : Transcript → OrderedChallenges)
    (real simulator : Transcript) (same : real = simulator) :
    publicSchedule decode real = publicSchedule decode simulator :=
  congrArg (publicSchedule decode) same

/-- Deterministic public postprocessing preserves the exact distinguishing
bound of a joint transcript, including correlations with its disclosed view.
This is a law about joint views, never a marginal-hiding claim. -/
theorem public_postprocessing {R S V U : Type} [Fintype R] [Fintype S]
    (real : R → V) (ideal : S → V) (encode : V → U) (ε : ℚ)
    (hprivacy : ∀ test : V → Bool,
      |mean (fun r => bit (test (real r))) - mean (fun s => bit (test (ideal s)))| ≤ ε) :
    ∀ test : U → Bool,
      |mean (fun r => bit (test (encode (real r)))) -
       mean (fun s => bit (test (encode (ideal s))))| ≤ ε := by
  intro test
  exact hprivacy (test ∘ encode)

/-- Current-source (SPLIT=10) correction to the older split-11 witness. -/
def first : List Fib := SerJoinOrderObstruction.first
def crossed : List Fib :=
  [0,1,2,3,4,5,6,7,8,10,9,11,12,13,14,15,16,17,18,19,20,21]

theorem witnesses : first.length = 22 ∧ first.Nodup ∧
    crossed.length = 22 ∧ crossed.Nodup ∧ first.toFinset = crossed.toFinset ∧
    (first.take 10).toFinset ≠ (crossed.take 10).toFinset := by decide

theorem no_legacy_factorization (batch : Finset Fib → Finset Fib) :
    ¬ (∀ qs : List Fib, qs.length = 22 → qs.Nodup →
      batch qs.toFinset = (qs.take 10).toFinset) := by
  intro h
  have ha := h first witnesses.1 witnesses.2.1
  have hb := h crossed witnesses.2.2.1 witnesses.2.2.2.1
  rw [witnesses.2.2.2.2.1] at ha
  exact witnesses.2.2.2.2.2 (ha.symm.trans hb)

#print axioms batch_lengths
#print axioms query_union
#print axioms fibre_union
#print axioms indices_set
#print axioms reads_nodup
#print axioms reads_coverage
#print axioms opens_coverage
#print axioms batches
#print axioms ordered_log
#print axioms simulator_schedule
#print axioms public_postprocessing
#print axioms witnesses
#print axioms no_legacy_factorization
end R1Z.PhaseWireOrdered16
```

## Stage 3 — source refinement components

`ProverCommitMaterialTransport16` closes the exact failed part-15 bridge:
explicit splitting of scalar-result and Vec.push results reduces the differing
monadic match shapes without unfolding the scalar sampler. `m31_accumulate`
and `qm31_accumulate` identify the finite recurrences with the generic
accumulator. `m31_extracted_prefix` and `qm31_extracted_prefix` compose those
identities with the extracted source-owned collectors and arbitrary-prefix
lemma. All remaining lengths are quantified; the only resource side condition
is `values.val.length + n ≤ Usize.max`, with `remaining.val = n`.
Errors and final state are preserved. These are exact owned-reference
collector laws, not an identification of the shipped borrowed caller/context.
The old Aeneas borrowed-loop context-join obstruction remains; no extraction
retry was run unchanged.

J8612 failed on unreduced matches before push; excluded. Changed J8613 passed
all four audits: exit 0, wall 1.84s, peak RSS 4141780 KiB, zero swaps, revision
`b4dfa41f2` plus exact source snapshot hashes. All accepted axioms are standard.
The warning-only unused simp arguments do not affect the accepted statement.

Verbatim adopted transport:

```lean
import R1Z.ProverCommitMaterialPrefix
/-! Explicit monadic case splits connect the extracted owned collectors to
arbitrary-prefix algebra. Scalar loops remain symbolic named callees. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaterialTransport16
open Aeneas Aeneas.Std Result AspisR1ProverMaterial14
open R1Z.ProverCommitMaterialRecursion (Hash State Values QValues)
open R1Z.ProverCommitMaterialPrefix

theorem m31_accumulate (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : Values) (state : State) :
    ProverCommitMaterialRecursion.finite hash domain n values state =
      accumulate (prover_commit_reference.limb_caller hash domain) n values state := by
  induction n generalizing values state with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitMaterialRecursion.finite, accumulate]
    cases hs : prover_commit_reference.limb_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        dsimp only
        cases hp : alloc.vec.Vec.push values value with
        | fail e => simp only [hp, bind_tc_fail]
        | div => simp only [hp, bind_tc_div]
        | ok fresh =>
          simp only [hp, bind_tc_ok, lift]
          exact ih fresh after

/-- Arbitrary existing prefix, arbitrary remaining length within Usize
capacity; errors and final state agree with the extracted owned reference. -/
theorem m31_extracted_prefix (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining : Usize) (values : Values) (state : State)
    (count : remaining.val = n) (room : values.val.length + n ≤ Usize.max) :
    erase (prover_commit_reference.collect_m31_owned hash domain state remaining values) =
      prepend values.val (collect (prover_commit_reference.limb_caller hash domain) n state) := by
  rw [ProverCommitMaterialRecursion.extracted_finite hash domain n remaining values state count,
    m31_accumulate]
  exact arbitrary_prefix _ n values state room

#print axioms m31_accumulate
#print axioms m31_extracted_prefix

theorem qm31_accumulate (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : QValues) (state : State) :
    ProverCommitMaterialRecursion.qmFinite hash domain n values state =
      accumulate (prover_commit_reference.qm31_caller hash domain) n values state := by
  induction n generalizing values state with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitMaterialRecursion.qmFinite, accumulate]
    cases hs : prover_commit_reference.qm31_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        dsimp only
        cases hp : alloc.vec.Vec.push values value with
        | fail e => simp only [hp, bind_tc_fail]
        | div => simp only [hp, bind_tc_div]
        | ok fresh =>
          simp only [hp, bind_tc_ok, lift]
          exact ih fresh after

/-- Arbitrary existing prefix, arbitrary remaining length within Usize
capacity; errors and final state agree with the extracted owned reference. -/
theorem qm31_extracted_prefix (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining : Usize) (values : QValues) (state : State)
    (count : remaining.val = n) (room : values.val.length + n ≤ Usize.max) :
    erase (prover_commit_reference.collect_qm31_owned hash domain state remaining values) =
      prepend values.val (collect (prover_commit_reference.qm31_caller hash domain) n state) := by
  rw [ProverCommitMaterialRecursion.qm_extracted_finite hash domain n remaining values state count,
    qm31_accumulate]
  exact arbitrary_prefix _ n values state room

#print axioms qm31_accumulate
#print axioms qm31_extracted_prefix
end R1Z.ProverCommitMaterialTransport16
```

### Returned material

`ProverCommitReturned16.assemble` composes the existing extracted owned
collectors in source order: c1; ten balanced mask-only columns; 1024 QM31 g
values and balancing; padding and balancing; final returned fields and nonce.
The inputs expose the preallocated buffers. It starts **after** nonce-store
reservation and seed derivation. It does not prove allocation success, field
canonicality, source-domain constants, nonce reservation, zeroization or a
shipped builder identity. Errors suppress partial returned material while
preserving their final expander state in the reference.

Independent extracted modules use distinct Lean QM31 types. `toBalance`,
`fromBalance`, `field_roundtrip` and `vector_roundtrip` preserve all four limbs
and arbitrary vector contents. `balance` calls the existing part-9 extracted
QM31 balancer through that adapter; no balancing recurrence is re-evaluated.
`assembly_oracle_support` proves the entire assembly result and final state
are unchanged under `SameFrames` on the one material domain, including all
errors. This is an owned reference composition and an oracle-support theorem,
not source identification. It cannot discharge RustProverRefinement alone.

J8614 failed because the QM31 balancer is in the separate extraction; J8615
added the typed adapter but exposed a missing raw-QM31 support bridge and
map-id proof; J8616 fixed support but left a missing explicit list argument.
All are excluded, with exact diagnostics retained. J8617 passed four audits:
exit 0, wall 2.09s, peak RSS 4150320 KiB, swaps 0, source revision `d863d8bc6`
plus exact source hash. `field_roundtrip` has no axioms; `vector_roundtrip`
uses `[propext, Quot.sound]`; both support results use only the standard three.

Verbatim adopted assembly and statements:

```lean
import R1Z.ProverCommitMaterialTransport16
import R1Z.ProverCommitMaterialSupport
import AspisR1ProverBalance9.Funs
/-! Assembly of the existing extracted owned components with retained state.
This reference begins after nonce reservation/seed derivation and allocation;
it is not a refinement certificate for the shipped outer builder. -/
set_option autoImplicit false
namespace R1Z.ProverCommitReturned16
open Aeneas Aeneas.Std Result AspisR1ProverMaterial14
open R1Z.ProverCommitMaterialRecursion (Hash State Values QValues)
open R1Z.ProverCommitMaterialSupport
abbrev Error := state_only_hiding.StateOnlyMaskBuildError

/-- Field-preserving transport between the independently extracted types. -/
def toBalance (q : aspis_core.field.QM31) : AspisR1ProverBalance9.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩
def fromBalance (q : AspisR1ProverBalance9.aspis_core.field.QM31) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def mapVec {α β : Type} (f : α → β) (v : alloc.vec.Vec α) : alloc.vec.Vec β :=
  ⟨v.val.map f, by simpa only [List.length_map] using v.property⟩

theorem field_roundtrip (q : aspis_core.field.QM31) : fromBalance (toBalance q) = q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

theorem vector_roundtrip (v : QValues) :
    mapVec fromBalance (mapVec toBalance v) = v := by
  apply Subtype.ext
  simp only [mapVec, List.map_map]
  change v.val.map (fun q => fromBalance (toBalance q)) = v.val
  simp only [field_roundtrip]
  exact List.map_id v.val

def balanceError : AspisR1ProverBalance9.state_only_hiding.StateOnlyMaskBuildError → Error
  | .ZeroPrivateEntropy => .ZeroPrivateEntropy
  | .ReusedMaskNonce => .ReusedMaskNonce
  | .MaskSampleExhausted => .MaskSampleExhausted
  | .TraceShape => .TraceShape
  | .Layout => .Layout

def balance (values : QValues) (dependent : Usize) (active : Array Bool 1024#usize) :
    Result (core.result.Result Unit Error × QValues) := do
  let (status, values) ← AspisR1ProverBalance9.prover_commit_reference.balance_qm31_owned
    (mapVec toBalance values) dependent active
  let status := match status with
    | .Ok () => .Ok ()
    | .Err e => .Err (balanceError e)
  ok (status, mapVec fromBalance values)

structure ReturnedMaterial where
  c1 : Values
  mask_only_c1 : alloc.vec.Vec Values
  g : QValues
  h1_padding : QValues
  mask_nonce : Array U8 32#usize

/-- Owned assembly, in the source's order. Supplied buffers expose allocation
and capacity responsibilities instead of silently assuming them. Partial
material is not returned on any error; the retained expander state is. -/
def assemble (hash : Hash) (domain : Slice U8) (state : State)
    (cells : Usize) (c1 : Values) (columns : alloc.vec.Vec Values)
    (g padding : QValues) (dependent : Usize) (active : Array Bool 1024#usize)
    (nonce : Array U8 32#usize) :
    Result (core.result.Result ReturnedMaterial Error × State) := do
  let (status, c1, afterC1) ←
    prover_commit_reference.collect_m31_owned hash domain state cells c1
  match status with
  | .Err e => ok (.Err e, afterC1)
  | .Ok () =>
    let (status, columns, afterColumns) ←
      prover_commit_reference.material_columns_owned hash domain afterC1 columns
        0#usize 10#usize dependent active
    match status with
    | .Err e => ok (.Err e, afterColumns)
    | .Ok () =>
      let (status, g, afterG) ←
        prover_commit_reference.collect_qm31_owned hash domain afterColumns 1024#usize g
      match status with
      | .Err e => ok (.Err e, afterG)
      | .Ok () =>
        let (status, g) ← balance g dependent active
        match status with
        | .Err e => ok (.Err e, afterG)
        | .Ok () =>
          let (status, padding, final) ←
            prover_commit_reference.material_padding_owned hash domain afterG padding
              0#usize dependent active
          match status with
          | .Err e => ok (.Err e, final)
          | .Ok () =>
            let (status, padding) ←
              balance padding dependent active
            match status with
            | .Err e => ok (.Err e, final)
            | .Ok () => ok (.Ok ⟨c1, columns, g, padding, nonce⟩, final)

theorem qm_raw_collection_support (left right : Hash) (domain : Slice U8)
    (same : SameFrames left right domain) (state : State) (count : Usize) (values : QValues) :
    prover_commit_reference.collect_qm31_owned left domain state count values =
      prover_commit_reference.collect_qm31_owned right domain state count values := by
  rw [ProverCommitMaterialRecursion.qm_extracted_finite left domain count.val count values state rfl,
    ProverCommitMaterialRecursion.qm_extracted_finite right domain count.val count values state rfl]
  exact qm_collection_support left right domain same _ values state

/-- All four families in the returned object use one retained material oracle.
Agreement on that domain transports the complete assembly, including errors,
balancing and final cursor; it requires no enumeration of 1024-row vectors. -/
theorem assembly_oracle_support (left right : Hash) (domain : Slice U8)
    (same : SameFrames left right domain) (state : State) (cells : Usize)
    (c1 : Values) (columns : alloc.vec.Vec Values) (g padding : QValues)
    (dependent : Usize) (active : Array Bool 1024#usize) (nonce : Array U8 32#usize) :
    assemble left domain state cells c1 columns g padding dependent active nonce =
    assemble right domain state cells c1 columns g padding dependent active nonce := by
  simp only [assemble,
    raw_collection_support left right domain same,
    indexed_columns_support left right domain same,
    qm_raw_collection_support left right domain same,
    indexed_padding_support left right domain same _ _ 0#usize _ _ (by decide)]

#print axioms field_roundtrip
#print axioms vector_roundtrip
#print axioms qm_raw_collection_support
#print axioms assembly_oracle_support
end R1Z.ProverCommitReturned16
```

### Section-wise Kani

The isolated snapshot calls the unchanged current `compact.rs` functions.
Only a cfg(kani) module is appended to its copy. Four focused checks pass:

| Target | Wall seconds | Peak RSS KiB | Exit | Swap |
|---|---:|---:|---:|---:|
| compact value, retained three-byte prefix | 9.354 | 532316 | 0 | 0 |
| nonzero high-half rejection, prefix unchanged | 3.245 | 376960 | 0 | 0 |
| expand one arbitrary compact value | 2.310 | 353352 | 0 | 0 |
| all six fixed node-slot offsets | 1.633 | 328448 | 0 | 0 |

All include unwinding assertions. Exact targets, source hashes/revision,
commands, stdout, timing, reservations and 6G/8G/no-swap/64-task scopes are in
`rust-attempts.json` and `receipts/`. `#print axioms` is N/A for Kani.
These are local serialization-section laws, not complete proof serialization,
semantic-message framing, multiproof traversal, RustSerializationJoin or a
Lean-to-Kani trusted import. The prefix is length three in these checks;
universal prefix transport above concerns the extracted material collectors.
The combined ordered-batch sorting/dedup check timed out at 600 seconds.
It was replaced by fixed-shape, source-valid 18-bit-key cases with unchanged
caps; the first (batch A, plain keys, kissat) also timed out at 600 seconds.
A smaller ordered-slicing/projection cut (before sort/dedup) timed out too.
All three are excluded; no success or counterexample is inferred. No further
fixed-shape cases were launched after that demonstrated solver obstruction.
The receipt's /usr/bin/time peak RSS for timed-out parents omits killed
children; the cgroup peaks below are the meaningful aggregate measurements.

| Excluded target | Exit | Wall seconds | Parent peak RSS KiB | Cgroup peak bytes | Swap |
|---|---:|---:|---:|---:|---:|
| combined ordered batch | 124 | 600.003 | 15836 | 4210159616 | 0 |
| fixed batch A plain | 124 | 600.003 | 16008 | 1002143744 | 0 |
| ordered projection cut | 124 | 600.094 | 16016 | 6614953984 | 0 |

These Kani jobs spend time in bounded symbolic verification, not native
finite-field elimination. Their dev-profile compiler output is Kani's MIR
input, not a debug arithmetic release gate. Native sampler validation uses
an optimized release binary. No cap was raised; all scopes are unchanged.



## Stage 4 — ordered public experiment and upgraded deployed endpoint

The initial direct-carrier obstruction has a useful resolution for the model:
its ROMView already includes the verifier transcript. `ProverCommitReencode16`
recovers the retained QueryScan order from those public entries, validates
length, distinctness and equality with the algebra's query set, then rebuilds
the 10+12 logical opening log. Malformed parses follow an explicit total
identity fallback. The decoder has no witness or private tape input.

`reindex_map` proves the exact new list, with its new multiplicities, can be
reconstructed from the old logical entries, since both cover the same global
read set. No new oracle query is introduced. `recover_algebra` pins the
projection. `encode_parts` proves the verifier transcript prefix and subsequent
observer-query suffix are preserved at a validated parse.

`experiment` wraps the adaptive observer's program **before** its queries and
transforms the final ROMView and decision together. `privacy_transport` proves
privacy for that transformed experiment with precisely the same ε; it is not
an argument based on marginal laws. `PrivacyR1HeadlineOrdered16.privacy_headline_ordered`
is the resulting model endpoint, with exactly the old error expression and
numerical bounds. J8620 first passed the transport core; J8624 passes the
completed prefix/suffix transport (exit 0, 5.05s, RSS 4149024 KiB, swap 0).
J8621 first passed the headline; J8625 replays it after that imported source
changed (exit 0, 8.10s, RSS 4184328 KiB, swap 0). These are changed dependency
inputs, not unchanged regression reruns. J8619 and J8622–8623 are excluded
syntax/normalization diagnostics; no failed declaration is adopted.

The final `PrivacyR1HeadlineDeployed.RustProverRefinement` now targets this
**ordered reencoded experiment**, replacing its initial legacy-log target.
Its only theorem proof binder remains `refinement`. It quantifies an independent
runtime and carries full public-run equality and observer decisions outside
the same realBad/selectedBad, including the ideal simulator join.
`privacy_headline_deployed` retains the original exact error expression, upper
bound and < 2^-100 conclusion. There is no specialization that identifies
Rust with the model in the adopted endpoint.

To charge the exceptions once, `ProverCommitModelCore16.core_privacy` exposes
the existing quotient model proof before the QueryScan/freshness allowances.
`read_bound` and `real_bad_mass` keep the huge concrete read universe symbolic.
The final proof transports that core through the ordered observer, applies
the two supplied whole-run joins, and uses the original model-level
`privacy_headline_admitted` numerical ledger. This is an extraction and
composition of existing model arguments, not new source evidence or a
reduction of the deployed obligation to a cryptographic assumption.

J8626 and J8628 hit concrete-specialization heartbeats; J8629–8630 are excluded
annotation syntax diagnostics. J8631 proves the abstract core; J8634 adds the
symbolic read bound; J8637 adds the abstract fixed-event mass bound (exit 0,
5.09s, RSS 4072708 KiB, swap 0). J8627 stopped at driver preflight because the
failed J8626 had no imported object: no Lean invocation occurred, and its
separate preflight receipt records unavailable resource fields as null.
J8632–8636 are excluded concrete-ROM specialization diagnostics. The old
reduction was replaced by named generic lemmas, not increased heartbeats or
memory. J8638 reaches the composed bound but has an addition-orientation
error; J8639 fixes it and removes diagnostic traces: exit 0, wall 16.97s,
peak RSS 4106448 KiB, swap 0, revision `5ada24a62` plus exact source SHA.
All adopted new audits use only subsets of the standard three axioms.

The 10-split witness is also reproduced by the unchanged native source sampler:
`sampler16-evidence.json`, revision `d863d8bc6`, exit 0, wall 8.05s,
peak RSS 569964 KiB, zero swaps, cargo run --release --offline -j4, same
6G/8G/no-swap/64-task cap and required RUSTFLAGS. It accepts both stable
orders swapping positions 9 and 10; their sets agree and their sorted first
batches differ. This is an arbitrary-squeeze-block source regression witness,
not a cryptographic-hash preimage or a universal source refinement. The probe
and all core sources/build script are pinned by hashes. #print axioms is N/A.

Verbatim completed reencoding definitions and statements:

```lean
import R1Z.ProverCommitFixedEndpoint
import R1Z.PhaseWireOrdered16
/-! Public reindexing and adaptive-observer transport. The transformed games
are constructed models, not a concrete Rust serialization certificate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReencode16
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.HvzkS R1Z.Batched
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable

/-- Select a logical read's bytes/answer from a previous encoding. -/
def fetch {C V : Type} [DecidableEq C] : List C → List V → C → Option V
  | a::tail, v::vs, c => if a = c then some v else fetch tail vs c
  | _, _, _ => none

theorem fetch_map {C V : Type} [DecidableEq C] (old : List C) (f : C → V)
    (c : C) (hc : c ∈ old) : fetch old (old.map f) c = some (f c) := by
  induction old with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons a old ih =>
    simp only [List.map_cons, fetch]
    by_cases ha : a = c
    · subst a; simp only [if_true]
    · rw [if_neg ha]
      apply ih
      rcases List.mem_cons.mp hc with he | he
      · exact False.elim (ha he.symm)
      · exact he

local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
abbrev Entry := List UInt8 × OracleAnswer

def reindex (ch : PhaseWireOrdered16.OrderedChallenges) (entries : List Entry) : List Entry :=
  (PhaseWireOrdered16.opens ch).map (fun c =>
    (fetch (PhaseWireLog2Bin.opens ch.algebra) entries c).getD ([], 0))

/-- The complete new ordered log, with its new multiplicities, is reconstructed
from the old log without any extra oracle query or private tape input. -/
theorem reindex_map (ch : PhaseWireOrdered16.OrderedChallenges)
    (entry : Fin 3 ⊕ RIdx → Entry) :
    reindex ch ((PhaseWireLog2Bin.opens ch.algebra).map entry) =
      (PhaseWireOrdered16.opens ch).map entry := by
  apply List.map_congr_left
  intro c hc
  have hold : c ∈ PhaseWireLog2Bin.opens ch.algebra :=
    (PhaseWireLog2Bin.opens_coverage ch.algebra c).mpr
      ((PhaseWireOrdered16.opens_coverage ch c).mp hc)
  rw [fetch_map _ entry c hold]
  rfl

/-- Recover the retained QueryScan order solely from public transcript entries.
Validation also makes malformed/rejected inputs explicit. This is a total
model decoder; source alignment of the transcript prefix is still required. -/
def recover {CommitHandle Aux : Type} (v : View K CommitHandle Aux R1Bat)
    (log : List Entry) : Option PhaseWireOrdered16.OrderedChallenges :=
  let q : Fin 8 → OracleAnswer := fun k =>
    (log[TranscriptR1.schedule.idxOf (.qb k)]?).getD ([], 0) |>.2
  let order := ((PhaseSamplerParserBin.scanned
    (PhaseQueryScanBin.stop PhaseSamplerParserBin.done q) q).1.accepted).map PhaseSamplerParserBin.fibre
  if hl : order.length = 22 then
    if hn : order.Nodup then
      if hs : order.toFinset = v.1.challenges.queries then
        some ⟨v.1.challenges, order, hl, hn, hs⟩
      else none
    else none
  else none

def encode {CommitHandle Aux : Type} (v : View K CommitHandle Aux R1Bat)
    (log : List Entry) : List Entry :=
  match recover v log with
  | none => log
  | some ch =>
    let transcriptLength := TranscriptR1.schedule.length
    let openingLength := (PhaseWireLog2Bin.opens ch.algebra).length
    log.take transcriptLength ++ reindex ch ((log.drop transcriptLength).take openingLength) ++
      log.drop (transcriptLength + openingLength)

theorem recover_algebra {CommitHandle Aux : Type}
    (v : View K CommitHandle Aux R1Bat) (log : List Entry)
    (ch : PhaseWireOrdered16.OrderedChallenges) (hr : recover v log = some ch) :
    ch.algebra = v.1.challenges := by
  unfold recover at hr
  dsimp only at hr
  split at hr
  · split at hr
    · split at hr
      · cases Option.some.inj hr
        rfl
      · cases hr
    · cases hr
  · cases hr

/-- Exact prefix/suffix transport at a validated public parse. In particular
reindexing neither changes nor discards an observer's later oracle queries. -/
theorem encode_parts {CommitHandle Aux : Type}
    (v : View K CommitHandle Aux R1Bat) (ch : PhaseWireOrdered16.OrderedChallenges)
    (front suffix : List Entry) (entry : Fin 3 ⊕ RIdx → Entry)
    (width : front.length = TranscriptR1.schedule.length)
    (parsed : recover v (front ++ (PhaseWireLog2Bin.opens ch.algebra).map entry ++ suffix) = some ch) :
    encode v (front ++ (PhaseWireLog2Bin.opens ch.algebra).map entry ++ suffix) =
      front ++ (PhaseWireOrdered16.opens ch).map entry ++ suffix := by
  unfold encode
  rw [parsed]
  simp [← width, List.take_append, List.drop_append, reindex_map]

section Transport
variable {CommitHandle Aux : Type}

def mapView (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry)
    (v : ROMView K CommitHandle Aux R1Bat) : ROMView K CommitHandle Aux R1Bat :=
  ⟨v.disclosed, encoding v.disclosed v.observerOracle⟩

def observer (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry)
    (adv : R1Adv K CommitHandle Aux) : R1Adv K CommitHandle Aux where
  prog := fun v log => adv.prog v (encoding v log)
  decide := fun v => adv.decide (mapView encoding v)

variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (N : Nat) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
local notation "model" => fsR1P W Pr N hN P Vp

def experiment (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry) :
    FSExperiments K CommitHandle Aux R1Bat F where
  Adversary := R1Adv K CommitHandle Aux
  RealRand := (model).RealRand
  IdealRand := (model).IdealRand
  real := fun h packing outputs adv x w r =>
    mapView encoding ((model).real h packing outputs (observer encoding adv) x w r)
  ideal := fun sim adv x r => mapView encoding ((model).ideal sim (observer encoding adv) x r)
  observe := fun adv v => adv.decide v

variable (encoding : View K CommitHandle Aux R1Bat → List Entry → List Entry)
instance real_finite : Fintype (experiment W Pr N hN P Vp encoding).RealRand :=
  inferInstanceAs (Fintype (model).RealRand)
instance real_nonempty : Nonempty (experiment W Pr N hN P Vp encoding).RealRand :=
  inferInstanceAs (Nonempty (model).RealRand)
instance ideal_finite : Fintype (experiment W Pr N hN P Vp encoding).IdealRand :=
  inferInstanceAs (Fintype (model).IdealRand)
instance ideal_nonempty : Nonempty (experiment W Pr N hN P Vp encoding).IdealRand :=
  inferInstanceAs (Nonempty (model).IdealRand)

/-- Adaptive programs receive the reencoded prefix before querying. Both games
and the final decision are transported together, with exactly the same ε. -/
theorem privacy_transport (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat) (ε : ℚ)
    (private_model : ZK_FSS h B outputs model x sim ε) :
    ZK_FSS h B outputs (experiment W Pr N hN P Vp encoding) x sim ε := by
  intro adv w hw
  exact private_model (observer encoding adv) w hw
end Transport

#print axioms fetch_map
#print axioms reindex_map
#print axioms recover_algebra
#print axioms encode_parts
#print axioms privacy_transport
end R1Z.ProverCommitReencode16
```

Verbatim ordered model endpoint:

```lean
import R1Z.ProverCommitReencode16
import R1Z.ProverCommitFixedObserver
/-! Explicit canonical admitted-domain specialization of the owned headline.
This fixes the mathematical builder, not its outstanding shipped Rust identification. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineOrdered16
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
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)
local notation "ordered" => ProverCommitReencode16.experiment W Pr 8 eight_pos
  (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
  ProverCommitReencode16.encode

/-- Model privacy after public ordered-log reencoding and adaptive observer
wrapping. This is not a proof of complete Rust proof-byte reconstruction. -/
theorem privacy_headline_ordered
 :
    ZK_FSS h B outputs ordered x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  have model := PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted
    template outputs x
  constructor
  · exact ProverCommitReencode16.privacy_transport _ _ _ _ _ _ _ _ _ _ _ _ model.1
  · exact model.2

#print axioms privacy_headline_ordered
end R1Z.PrivacyR1HeadlineOrdered16
```

Verbatim abstract core and fixed-event lemmas:

```lean
import R1Z.ProverCommitQuotientPrivacy
import R1Z.PrivacyR1FinalProtocolHistoryReal
import R1Z.PrivacyR1FinalProtocolHistory
import R1Z.QueryScanFreshNumerics

/-! Real-law-free endpoint with a proved scan-freshness numerical allowance.
The conservative internal coupling budget is dominated by that allowance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitModelCore16
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
local notation "K" => AspisWideTower.WideExact
variable {CommitHandle Aux : Type} {F : Subfield K}
variable (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
theorem core_privacy
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_quotient_fibres : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        quotientDecode (fun e => ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2) e = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
 :
    ZK_FSS h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
      (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x) (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂) := by
  let W := (wire base ((base.pubBytes x).length) h B outputs x).toWire
  let Pr := (prover base ((base.pubBytes x).length) h B outputs x seed).toProver
  let R : RomModel W := RomFiniteBin.rom (baseWire base) (RomGrammarBin.bound ((base.pubBytes x).length))
  have hin : ∀ w : h.Instance, RAddrIn W Pr R h B outputs x w :=
    RomGrammarBin.address_domain (baseWire base) _ Pr h B outputs x
      (PhaseProtocolCoverageBin.read_coverage base _ h B outputs x seed (Nat.le_refl _))
  have hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w :=
    fun w => (causal_iff W Pr h B outputs x w).mpr
      (causal_premise base _ h B outputs x seed w)
  have hb : RCommitBytes W Pr := PrivacyR1Final.commit_source W Pr
    (PrivacyR1FinalProtocol.commitment_grammar base _ h B outputs x seed)
  have hop := PrivacyR1Final.wire_batches W Pr R_wire_D80_batches
  have hcom := (com_log_iff W Pr hb R_wire_coin_carrier h B outputs x).mpr R_wire_D80_ordered_log
  have hz := R1Z.ProverCommitQuotientPrivacy.privacy_R1_games_quotient W Pr 8 (by decide) h B hB outputs x
    hpub builder_refinement_D46_D51 (rows01 base _ h B outputs x)
    (R1J.PrivacySamplerSpend.samplerLaw_of_spend W (rows01 base _ h B outputs x)
      (algebraMap R1J.SamplerLawSpend.QF K) (RingHom.injective _)
      (sampler_source base _ h B outputs x))
    R hin hc hb cF (by
      intro τ
      convert R_commit_quotient_fibres τ using 2
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl) L₁ L₂ R_commit_exhaustion
    R_commit_counter₁ R_commit_counter₂ R_commit_stream₁ R_commit_stream₂
    R_wire_coin_carrier hop hcom
  have hm : ZK_FSS h B outputs (fsR1P W Pr 8 (by decide)
      (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x) (modelError W Pr L₁ L₂) := by
    simpa only [modelError, abR1P, abR1, Nat.cast_ofNat, Nat.cast_pow,
      Nat.cast_zero, zero_mul, zero_div, pow_two] using hz
  exact hm

/-- Keep the large concrete finite read universe symbolic at specialization. -/
theorem read_bound (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (L₁ L₂ : ℕ) (count : RCommitCount L₁ L₂)
    (blocks₁ : Pr.E₁ ≤ 2*L₁) (blocks₂ : Pr.E₂ ≤ 2*L₂) :
    8 * n1 W Pr ≤ 2^25 := by
  have hn := R1Z.GamesR1PBin.n1_le W Pr L₁ L₂ count blocks₁ blocks₂
  norm_num at hn ⊢
  omega

/-- The generic ROM environment prevents concrete domain normalization when
only its fixed-event mass is needed by the runtime endpoint. -/
theorem real_bad_mass
    (seed : R1ProverP K CommitHandle Aux F (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (w : h.Instance) :
    eventMass (fun r => ∃ k, QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w k r) ≤
      QueryScanRealLazyBound.lazyBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver) +
        8 * scanProbability := by
  let W := (wire base ((base.pubBytes x).length) h B outputs x).toWire
  let Pr := (prover base ((base.pubBytes x).length) h B outputs x seed).toProver
  let R : RomModel W := RomFiniteBin.rom (baseWire base) (RomGrammarBin.bound ((base.pubBytes x).length))
  have hin : RAddrIn W Pr R h B outputs x w :=
    RomGrammarBin.address_domain (baseWire base) _ Pr h B outputs x
      (PhaseProtocolCoverageBin.read_coverage base _ h B outputs x seed (Nat.le_refl _)) w
  have hc : RCausal W Pr h B outputs x w :=
    (causal_iff W Pr h B outputs x w).mpr (causal_premise base _ h B outputs x seed w)
  have hb : RCommitBytes W Pr := PrivacyR1Final.commit_source W Pr
    (PrivacyR1FinalProtocol.commitment_grammar base _ h B outputs x seed)
  exact QueryScanRealLazyBound.real_bad_union_mass W Pr R 8 (by decide) h B outputs x w
    hin hc hb counter₁ counter₂

#print axioms real_bad_mass
#print axioms read_bound
#print axioms core_privacy
end R1Z.ProverCommitModelCore16
```

Verbatim final deployed endpoint (supersedes Stage 1's initial target):

```lean
import R1Z.ProverCommitFixedEndpoint
import R1Z.ProverCommitReencode16
import R1Z.ProverCommitModelCore16
import R1Z.ProverCommitFixedObserver
/-! Explicit canonical admitted-domain specialization of the owned headline.
This fixes the mathematical builder, not its outstanding shipped Rust identification. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineDeployed
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
local notation "raw" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)

local notation "source" => ProverCommitReencode16.experiment W Pr 8 eight_pos
  (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
  ProverCommitReencode16.encode

/-- Equality of the full observable execution and the observer's decision,
not merely equality of acceptance or a hash. The independently supplied
runtime must include builder/checker/retry, ordered wire and oracle history
in its FS experiment. No concrete Rust instance is supplied here. -/
structure WholeRunJoin {R M : Type} [Fintype R] [Fintype M]
    (runtime : R → ROMView K CommitHandle Aux R1Bat × Bool)
    (model : M → ROMView K CommitHandle Aux R1Bat × Bool)
    (bad : Fin 8 → M → Prop) where
  cp : Coupling R M
  agreement : ∀ s, ¬ (∃ i, bad i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s)

def WholeRunJoin.tests {R M : Type} [Fintype R] [Fintype M]
    {runtime : R → ROMView K CommitHandle Aux R1Bat × Bool}
    {model : M → ROMView K CommitHandle Aux R1Bat × Bool}
    {bad : Fin 8 → M → Prop} (join : WholeRunJoin runtime model bad) :
    ModelExecutionJoin (fun r => bit (runtime r).2) (fun m => bit (model m).2) bad where
  cp := join.cp
  agreement := fun s hn => congrArg (fun run => bit run.2) (join.agreement s hn)

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

/-- The explicit deployed obligation. Both sides include the complete public
view, ordered observer history and observer decision. The exceptions are the
existing realBad/selectedBad, not predicates chosen by the implementation. -/
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (WholeRunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w))) ∧
  (∀ adv : rust.Adversary, Nonempty (WholeRunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad))

attribute [local irreducible] PrivacyR1AcctBasis.basis
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100 := by
  have model := PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted
    template outputs x
  have caller := ProverCommitOwnedEndpoint.caller_law template input outputs x
  obtain ⟨hc₁,hc₂,hs₁,hs₂,hcount,hb₁,hb₂⟩ := ProverCommitCallerInstance.budgets Pr caller
  have hM := ProverCommitModelCore16.read_bound W Pr L₁ L₂ hcount hb₁ hb₂
  have hk := QueryScanFreshNumerics.lazy_budget_le_fresh hM
    (Nat.succ_le_succ (Nat.zero_le (8 * n1 W Pr)))
  constructor
  · intro adv w hw
    have hr := QueryScanRealLazyJoin.join_le _ _ _
      (Classical.choice (refinement.1 adv w hw)).tests
      (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr))
      (ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
    have hi := scan_coupling_le _ _
      ((Classical.choice (refinement.2 adv)).tests.toScanCoupling
        (fun i => QueryScanIdealHistory.selected_bad_mass i))
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
    obtain ⟨hpub, hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
    have core := ProverCommitModelCore16.core_privacy base h B outputs x seed hB hpub hs
      ProverCommitSourceDecoder.quotientFibreSize (by
        intro τ
        convert ProverCommitCallerInstance.fibres Pr caller τ using 2
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      L₁ L₂ (ProverCommitCallerInstance.exhaustion Pr caller)
      hc₁ hc₂ hs₁ hs₂ coins
      (PhaseWireLog2Bin.batches input outputs x template decode)
      (PhaseWireLog2Bin.ordered_log input outputs x template decode) hcount hb₁ hb₂
    have mid := ProverCommitReencode16.privacy_transport _ _ _ _ _ _
      ProverCommitReencode16.encode _ _ _ _ _ core
    have hmid := mid (RomObserverBin.observerMap rust observer_program adv) w hw
    have t₁ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (realTest h B outputs source (RomObserverBin.observerMap rust observer_program adv) x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
    have t₂ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
      (mean (idealTestS rust adv x (simE (h).transport B outputs x)))
    rw [abs_sub_comm] at hi
    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486) +
        modelError W Pr L₁ L₂) + 8 / (2 : ℚ)^486 :=
          t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) :=
          QueryScanFreshNumerics.amount_identity _ _ _
         _ ≤ _ := add_le_add (le_refl _) hk
  · exact model.2

#print axioms WholeRunJoin.tests
#print axioms privacy_headline_deployed
end R1Z.PrivacyR1HeadlineDeployed
```

## Diffs and residual boundary

`formal-additions.diff` records all new formal modules against the research
base. `deployed-ordered-upgrade.diff` records the initial-to-final deployed
statement and proof change. These are in the part-16 evidence directory.
The model change is explicit, not a deletion-only source-refinement claim.
No old shared module/source/object, concurrent-worker file, production source,
feature, wire constant, security target, wallet or key is modified.

**Target not yet established for the shipped prover.** Remaining obligations:

1. Supply the independently represented shipped experiment and prove its
   RustProverRefinement instance, including builder, checker, early-stop retry,
   visible errors, shared-oracle callbacks, serialization and observer.
2. Align `recover` with the actual retained transcript prefix on success and
   abort. The total decoder and validated-parse transport do not establish this
   concrete parser/history property by themselves.
3. Align the per-batch logical `reads` order with the exact dV_frozen2 tree and
   node traversal, and prove complete proof-byte reconstruction. Per-tree keys
   are sorted after the ordered 10+12 split, but logical reads still use the
   fixed finite-set list order. The old serialization residual is not declared
   discharged; the timed-out Kani ordered-block cases provide no certificate.
4. Connect the extracted owned collector and assembled object to the shipped
   borrowed loops/context, nonce reservation, seed/entropy/allocator boundaries
   and final object disposal. The prior Aeneas loop-context join failure and
   the all-family callback obligations remain. No unchanged extraction rerun
   is claimed.

The next concrete deliverable is an owned outer assembly extraction with a
source-iteration/context refinement, plus a small source traversal reference
whose standard-library sorting boundary can be certified independently of
symbolic Vec allocation. The four accepted codec checks, universal extracted
prefix bridges, returned-reference support and conditional deployed theorem
are reusable components, not a complete deployed privacy certificate.

No frozen ELF or SBF artifact was rebuilt. Historical artifact pins are
inherited only within their original scope. No full frozen manifest replay is
claimed for these additive model changes; the final cached dependency audit
is recorded below after all adopted sources are frozen.
