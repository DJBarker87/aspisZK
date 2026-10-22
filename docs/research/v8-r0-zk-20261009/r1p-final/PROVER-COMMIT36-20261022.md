# Prover commitment continuation 36

**Target not yet established. Intended trust list: P7, TrustedStd, E1
(successful OS RNG draws), E2 (atomic create-if-absent and persistence).**
The intended endpoint uses the D146 deployed statement image and D143
published-data scope, excluding timing and other side channels. No new
endpoint or removal of RustProverRefinement is claimed.

Actual base: `e91b035a1339e76376ec024ac173418327230462`.
Branch: `codex/cx-prover-commit36-20261022`. No shipped source changed.

The new component results retain E1 where used and introduce the named E2
contract with a consistent model instance; the actual deployed theorem's
premises are unchanged. No source-refinement assumption is discharged.

## Stage 1: private reservation membership

`R1Z.ProverCommitLedger36` implements private ledger membership. The
adversarial schedule selects faults and added paths using only the call
index, kind and prior statuses. Initial ledger and additions are independent
of the private tape by the strategy interface. Membership is evaluated
privately after additions; occupied paths return AlreadyExists, fresh paths
either fail or are created. Existing entries are retained. A created entry
survives every later write/fsync fault, including directory-open failures.

The model re-proves `fail_closed` and `failure_replay` for the environment
prefix, with arbitrary witness-dependent successful continuations.
`duplicate_path` covers an occupied nonce address; it stops before writes.
These are membership/control model theorems. The module does not claim a
native filesystem instance, byte-content refinement, SHA-256 address law,
or whole simulator/publication theorem. E2 is an explicit named Prop
contract, not a Lean axiom; no native instance has been assumed as proved.

J9128 is a rejected proof draft (a split tactic selected the fault match
instead of ledger membership). J9129 compiles the corrected module: exit 0,
2.09 s, peak RSS 4,164,956 KiB, zero swaps. All eight new theorem audits
use only standard axioms. Exact source snapshots, dependency-object hashes,
commands and raw receipts are under
`evidence/prover-commit36-20261022/lean/`. Each attempt uses its own capped
scope, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean
`-M7000`; no cold dependency build or full regression runs.

## Remaining stages

The requested numerical collision bound is obstructed at the native address
law described below. This stops item (1) before its numerical release gate;
it is not a claim that the whole item is complete.

Complete native publication, source-to-FSExperiments conversion, concrete
shippedProverExperiment and both WholeRunJoins remain open. The actual
endpoint is unchanged; no premise deletion has occurred.

## Demonstrated obstruction: E1 does not make hashed paths uniform

The source at `crates/aspis-prover/src/state_only_entropy.rs:905–919`
constructs the filename by SHA-256 of
`b"aspis:state-only:attempt-reservation:v1" || mask_nonce`, hexadecimal
encoding and `.burn`. The hex encoding is lossless; the hash is the issue.
No shipped source is modified by this job.

For N = 2^256, a fixed address function H and a fixed ledger path p, the
raw uniform-nonce collision probability is
`|{n : H(n) = p}| / N`. E1 supplies the denominator and the input law;
it supplies no bound on that preimage count. One *path entry* can have
several preimages. Byte-blind choice of p does not establish a bound on
the number of such preimages.

`ProverCommitPathMass36.E1_address` proves the exact E1 push-forward.
`constant_address_mass` proves that a constant address function gives
mass 1 for one fixed entry. `no_E1_only_path_bound` disproves a universal
E1-only bound of 1/2^256 for address functions. `entries_bound` proves
the entry-count union bound with the missing push-forward hypothesis
**visible**, and `bijective_address_mass` shows a permutation would suffice.
No permutation property of SHA-256 is assumed or claimed.

`ProverCommitE2Witness36.model_E2` constructs a consistent atomic filesystem
model with Nat-valued file contents and durable-data retention.
`E1_E2_without_uniform_paths` proves that E1 and this E2 instance coexist
with failure of the generic uniform-address bound. E2 cannot repair the
missing address law: atomic create/persistence do not constrain address
hashing. This is a countermodel to the proposed **generic inference from
E1/E2**, not a demonstrated bad SHA-256 path, not an actual privacy attack,
and not a proof that the desired concrete native bound is false.

J9131 compiles all five address-mass theorems: exit 0, 1.88 s, peak RSS
4,152,568 KiB, zero swaps. J9133 compiles both E2 consistency/countermodel
theorems: exit 0, 1.91 s, peak RSS 4,153,900 KiB, zero swaps. All audits use
only [propext, Classical.choice, Quot.sound]. J9130 and J9132 are rejected
elaboration drafts; diagnostics and exact source bytes are retained.

**Exact next interface:** prove a native reservation-address push-forward
bound, for adversary-chosen initial/added path entries and all prior
contexts, including the generated nonce's nonzero rejection and retry law.
The simplest raw-draw interface would be

```lean
∀ context p,
  conditionalMass okLaw context
    (fun raw => nativeReservationAddress (raw 0) = p) ≤ 1 / (2 : ℚ)^256
```

This statement is an obligation, not an added hypothesis of the endpoint.
It cannot be discharged by merely rewriting E1. The source function's
preimages, or a different justified joint hash/nonce probability law, must
be accounted for. The count of 96-byte RNG draws also differs from the
eight prover attempts (up to sixteen entropy draws per generation).
No rejection-conditioning loss or additional draw factor is silently
dropped here, and no OS/fs probability charge is introduced.

D92's existing ruling models the protocol `HashFn` callback as the shared
random oracle. The reservation implementation instead calls `Sha256`
directly. Applying a ROM argument to this domain would require its concrete
source-to-oracle transport and a bound with prior oracle/precomputation
history accounted for; merely renaming this direct call to a uniform path
would not prove that interface. No new hash regularity assumption, E3,
TrustedStd field or cryptographic trust item is installed.

Per the user's stop rule, work stops at this demonstrated inference gap.
Native publication (proof bytes, ordered tables, merge, early errors),
observation conversion, concrete experiments and both WholeRunJoins remain
open. The membership/control model is reusable, but does not discharge
those source refinements. The security target remains unchanged and is
**not yet established**.

## Actual endpoint before/after: unchanged

The active fuel-accounted endpoint is `ProverCommitDeployedFuel22`.
The older `PrivacyR1HeadlineDeployed` and TrustedStd are also byte-identical
to the task base; complete source snapshots, SHA-256 and the empty diff
are retained under `endpoint/`. No statement-domain or environment
quantifier change is installed into either endpoint. D146 and D148 remain
the intended eventual quantifiers, not a claim about the existing theorem.
No budgets, events, witness/adversary restrictions or conclusions changed.
The following is the verbatim theorem statement before and after.

Before:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Final verification and handoff

J9134 is the one final focused audit of all fifteen new top theorems. It
imports the final new dependency closure, prints every theorem's axioms and
prints the exact E2/address interfaces: exit 0, wall 1.76 s, peak RSS
4,129,592 KiB, zero swaps. Every accepted theorem uses only a subset of
[propext, Classical.choice, Quot.sound]. No sorry/admit/native_decide or
new recursion/heartbeat settings occur in the final modules.

All seven attempts J9128–J9134 have exact targets, source SHA-256 snapshots,
dependency fingerprints and object hashes, commands, exits, wall times,
RSS, swaps, full axioms output and rejected-draft diagnostics in
`evidence/prover-commit36-20261022/lean/attempts.json` and raw receipts.
The recorded task-base revision plus source overlay hashes identifies each
attempt. `final-proof-audit.json` additionally checks the committed proof
sources at `a1889ba35` plus the exact additive J9134 audit module against
host sources and all retained audit dependency objects; all match.
No inherited shared module was overwritten. This job's own changed module
versions/objects were snapshotted in its branch-specific host directory by
the launcher helper before replacement.

No native/Kani, dense arithmetic, SBF or runtime gate ran. No Rust source
changed, so the shipped-file ELF rule is not triggered. The complete
crates/programs source hash inventory is retained in
`shipped-sources-unchanged.json`. Existing runtime/artifact checks are
reused, not rerun. No full frozen manifest replay ran because the numerical
native-address preflight is not green. No claim of a formal release replay
is made.

All task compilation jobs finished. No binaries, .olean, LLBC or ELFs are
committed; no local target directory or wallet/account key was created.
No key was deleted or altered. Nothing was pushed or merged.

Completed checkpoints: `722486dc5` (membership/control model), `a1889ba35`
(address-law obstruction). The exact next deliverable is the native
reservation-address push-forward interface above. Subsequent native
publication, observation conversion, both WholeRunJoins and the endpoint
without RustProverRefinement remain open. Next unused Env J attempt: J9135.
