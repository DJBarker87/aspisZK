# Prover commitment continuation 41

**Target not yet established.** The public-prefix conditional ROM law and
mixed-read agreement are proved locally, but their concrete private-derived
bounds and successful source continuation are not yet joined. The selected
64-byte native API has a bounded control check and a translated structural
owner; its Lean bridge is still open. Work stopped on **exhaustion of every
explicitly assigned Env J receipt number**, not a newly demonstrated privacy
counterexample. Trust items and the deployed endpoint are unchanged.

## Stage 1: conditional frozen-table law

`ProverCommitConditionalRom41.conditional_law` proves the exact ROM
programming law jointly with an arbitrary observation determined by frozen
coordinates. Its indicator form includes impossible observations without
conditional division. `history_fiber` proves both directions of equality
with an ordered adaptive history when that history's addresses are frozen;
`programmed_history` applies this to frozen programming. Repetitions and
termination are preserved, and a retained rejected-attempt prefix is not
removed from the list. These generic results do not yet discharge the
concrete private continuation or replace `EventsR1PBin.hit_cm`.

J9187–J9188 are rejected namespace drafts. J9189 compiles the three final
theorems, exit 0, wall 1.83 s, peak RSS 4,043,272 KiB, zero swaps. All
printed axioms are subsets of [propext, Classical.choice, Quot.sound].
The exact target, source SHA, dependency fingerprint, source revision plus
overlay, commands and raw receipts are retained under
`evidence/prover-commit41-20261022/lean/`. No inherited module was overwritten;
only part-41 drafts were replaced and snapshotted on the host.

## Stage 2: concrete public prefix and mixed read agreement

`ProverCommitPublicPrefix41` instantiates the conditional law at the finite
byte ROM. Its context retains the exact prior adaptive history plus three
ordered public reads: `H(pub)`, the precommit binding, and the attempt binding.
The public nonce policy is an arbitrary function of the fixed prior history.
`reads_of_slice` connects a coherent digest/first-answer slice to the actual
dependent binding addresses; `grammar_binding1` identifies the second grammar
branch. `raw_off_history` proves that outside the existing raw suffix memo
event, no address with that seed suffix is an earlier adversary query.
The law is joint and unnormalised, not a claim of independent public answers.

`ProverCommitPublicCoins41` normalises public answer positions to the values
retained in the conditional context, leaving their independent spare coins
unused. It proves causality, the conditional table law and actual read
agreement. Public reads need memo coherence; only private positions require
freshness and first-occurrence separation. `ProverCommitMixedReads41` also
proves agreement with consistent repeated reads. These are generic read
agreements; concrete private-derived hit/pair bounds and successful source
continuation transport remain to be instantiated.

`ProverCommitBindingErase41.opened_log` proves that substituting both public
binding answers leaves the entire ordered verifier commitment opening log
unchanged, for every opened root, leaf and node. It also permits arbitrary
changes to all three secret slots at this local address boundary. No claim
about whole proof equality follows from that local result alone.

Accepted focused targets: J9195 `ProverCommitPublicPrefix41` (1.91 s,
4,162,116 KiB); J9193 `ProverCommitMixedReads41` (1.79 s, 4,154,696 KiB);
J9197 `ProverCommitPublicCoins41` (1.79 s, 4,158,316 KiB); J9198
`ProverCommitBindingErase41` (1.81 s, 4,156,388 KiB). All exit 0, zero swaps,
standard axioms only. Rejected drafts J9190, J9192, J9194, J9196 are retained;
J9191 is an accepted predecessor of J9195. MixedReads was rebuilt at J8136 against the final PublicPrefix object
before the final dependency audit.
No old HitFresh theorem is falsely claimed discharged on the new carrier.

## Verbatim active endpoint before/after: unchanged

The full original module binders and body are retained in identical
`endpoint/before.lean.txt` and `endpoint/after.lean.txt` snapshots.
The active statement quantifier remains `x : Statement K CommitHandle`;
the arbitrary `rust : FSExperiments K CommitHandle Aux R1Bat F` and
`RustProverRefinement` premise remain. The D146 deployed statement-domain
restriction has not been silently installed without the source join.

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


## Stage 3: selected 64-byte native entropy owner (partial)

The exact native `StateOnlyAttemptSecrets::generate_for_mask_nonce` body is
pinned verbatim in `harness/native-generate.rs`, from
`crates/aspis-prover/src/state_only_entropy.rs`. The new `harness/owner.rs`
uses structural recursion, a separate public nonce argument and two private
32-byte blocks. It stops on an OS error, on sixteen rejected candidates or
on success. It does not sample a nonce. The zero public nonce guard precedes
all fill calls.

`proofs::selected_api_owner` checks the native loop against that reference,
including returned nonce, both private blocks, status, call count and raw
return count. The successful primitive draws use arbitrary first bytes in
the two otherwise zero blocks: all zero/nonzero **control patterns** are
represented, but this is a bounded compressed-byte control check, not a
proof for arbitrary 64-byte draws or an E1 probability law. The public nonce
is an arbitrary full 32-byte value. Zeroizing storage and fill are explicit
primitive substitutes; zeroization and actual OS internals are not certified.
The separate zero-nonce harness was not run because that control case is
already included in the accepted owner comparison.

Native receipt `selected-api-owner-v1`: exit 0, 53.871 s, peak RSS
3,837,976 KiB, scope peak 3,942,617,088 bytes, zero swaps; 391 checks pass.
Time was expected in Kani compilation and symbolic loop/control checking,
not field arithmetic or proof generation. Kani reports its verification MIR
build as dev/unoptimised; no heavy arithmetic execution ran. Charon extraction
of the owned reference used `--release --jobs 4`, opt-level 3, with the
required linker flag. No arithmetic gate was launched in a debug profile.

The first Charon command (`owner41-charon-v3`) exits 101 at 0.157 s because
its start-from crate name was wrong; that command was corrected rather than
rerun unchanged. `owner41-charon-v4` exits 0, 0.150 s, peak RSS 158,048 KiB,
zero swaps, LLBC `has_errors=false`. `owner41-aeneas-v4` exits 0, 0.283 s,
peak RSS 62,304 KiB, zero swaps. The LLBC is recorded by SHA256 and size
only. Aeneas-generated Types/Funs text is preserved in `unverified/`; it
was **not Lean-compiled** and is excluded from the final accepted proof cone.
No new trust item is inferred from a passing translation or bounded check.

The source owner is therefore partial: the exact next interface is the
byte/zero-test and stateful primitive bridge from
`AspisR1PublicNonce41.owner.generate` (public nonce, two raw blocks, sixteen
candidates, retained state) to `ProverCommitPublicNonce40.generate`, followed
by composition with the E2 reservation-history owner. The selected native
source is not replaced by the 96-byte adapter.

## Demonstrated build-number obstruction

The user assigned J9187–J9199, then J9200–J9399, and also the legacy
J8100–J8399 allocation. J9200 and J9201 were refused by the launcher with
exit 65 because receipts for other modules already existed. No compiler ran
for those two submissions. Their attempted source snapshots are retained,
but the other modules' existing logs are **not** attributed to this work.
The collector records `compiler_launched=false`, empty compiler status and
null compiler wall/RSS/swap/axioms for both refusals.

The read-only inventory then found all 200 later numbers occupied and just
two unused numbers in the explicitly assigned legacy range: J8136 and J8137.
Those were used for the dependent rebuild and final audit. The final
`assigned-range-inventory.json` records receipt/source pins for all 513
assigned numbers: **none remains unused**. The pre-audit inventory is also
retained. No unassigned number was used, no receipt was overwritten, and no
unchanged source/dependency pair was rerun. A request for a further range
was issued while independent evidence collection continued; no reply had
arrived at this handoff.

J9199 is a rejected attempt at additional raw-domain separation. Its
corrected draft is in `unverified/ProverCommitRawFresh41.lean.txt`; it has no
accepted compiler result and is not imported by any delivered proof module.
J9201's refusal did not validate that draft. This is distinguished from the
accepted generic suffix exclusion `PublicPrefix41.raw_off_history`.

After a new allocation, the exact mathematical deliverable for item (1) is
the concrete `gAddr`/`attVec` instance of the public-normalised read law,
with the public nonce policy and both memo answers retained, proving the
private-derived hit/frozen/pair bounds on that conditional carrier and then
the successful continuation with the ledger/history state. The generic
`run_eq` hypotheses are proof obligations, not newly trusted callbacks.
The existing bounds on mask expansion, D-seed, source expansion, salted
leaves, Merkle nodes and transcript reads have not been replaced by raw-seed
counting, nor claimed transported before that instance exists.

## Final audit, assumptions and remaining work

J8136 rebuilds `R1Z.ProverCommitMixedReads41`: exit 0, 1.80 s,
4,154,872 KiB RSS, zero swaps. Its new dependency fingerprint reflects the
extended PublicPrefix module, so this is not an unchanged replay. J8137
compiles `R1Z.ProverCommitAudit41`: exit 0, 1.72 s, peak RSS 4,143,964 KiB,
zero swaps. It prints axioms for **all 20 new top theorems** and the existing
deployed endpoint: every one is a subset of
[propext, Classical.choice, Quot.sound]. `final-proof-audit.json` checks the
six final local module SHA256 values and all imported object hashes used
by this audit against the installed host sources/objects. The exact task
base is `48a072e70` (full revision in `revision.txt`); each receipt identifies
its source bytes and dependency objects, including uncommitted overlays at
that stage. No evidence is attributed to an unrelated clean checkout.

All Lean jobs used the pinned Env J launcher and -M7000, in capped scopes
with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0 and TasksMax=64.
Native Kani/Charon/Aeneas jobs used the same cgroup limits and
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. The observed host reservation plus
these scopes remained below 55 GiB. No session went silent for twenty
minutes. No killed-by-memory job, uncapped build, local Lean compile or
unchanged full regression ran. There is no full-manifest or formal release
claim: the source/experiment joins remain open.

Trust list remains P1, P7, TrustedStd, E1 (successful OS draws uniform and
independent), E2 (atomic durable ledger). There is no nonce distribution,
ledger-size cap, OS/fs availability assumption or new trust field. D143
observables remain public statement bytes, submitted proof bytes and the
adversary's own oracle answers; timing and other side channels remain
outside the announced contract. The part-40 conditional numerical envelope
and zero term are retained unchanged; they are not yet installed into a
deployed theorem.

No deployed premise was removed. Complete native simulator publication,
source-to-FSExperiments conversion, `shippedProverExperiment`, both concrete
WholeRunJoins and the endpoint without `RustProverRefinement` remain open.
No wrapper was introduced that assumes any of those conclusions. The
before/after endpoint above is verbatim and unchanged.

All **491** tracked files under crates/programs match the task base byte for
byte (`shipped-sources-unchanged.json`). The native/reference harness lives
only under evidence. The shipped-file rule does not trigger an ELF rebuild;
existing ELF evidence is reused solely for unchanged shipped artifacts.
No binary, .olean, LLBC, ELF, tarball or local target directory is committed.
No wallet/account keys or funds were created, modified or removed. No push
or merge was performed.

Stage commits: `c285ee7d4` (conditional ROM/history law), `8b7275bad`
(public binding preservation and mixed reads); the final commit contains the
selected native owner evidence, coherent focused audit and this obstruction
handoff. **Target not yet established.**
