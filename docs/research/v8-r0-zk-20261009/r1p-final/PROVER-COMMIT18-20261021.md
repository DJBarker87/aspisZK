# Prover commitment part 18 — shipped experiment audit

Base `c35b7b481`; branch `codex/cx-prover-commit18-20261021`.

## Target and boundaries

Construct the actual shipped experiment, prove both fixed-event whole-run
joins and specialize the deployed endpoint. Concurrent-worker modules
SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease are untouched.
No production source or security contract is changed.

## Stage 1 — entropy and retained state

The source entry point calls `StateOnlyAttemptSecrets::generate`, which
performs up to sixteen 96-byte OS draws. Each draw contains three 32-byte
blocks; a zero block rejects the whole draw. OS error aborts immediately;
sixteen rejected draws return `RepeatedZeroBlock`. Neither error is a
`MaskSampleExhausted` retry. `prove_masked_retrying_with` maps entropy failure
to `Error::Entropy` and aborts rather than using another of its eight attempts.

`ProverCommitEntropy18` defines this control-flow adapter with explicit OS
error and retained draw state. Its successful result is the existing `SecP`
carrier. The all-zero and OS-failure paths remain errors. No OS law, source
translation or full FS-experiment claim follows merely from this definition.

Validation and remaining stages are recorded incrementally below.

J8656 exposed two syntax/type-annotation errors and is excluded. Changed-source
J8657 passes all seven audits: exit 0, wall 2.35s, peak RSS 3,498,544 KiB,
swaps 0; revision `c35b7b481` plus the exact source hash in `lean/`.
`no_total_success_adapter` has no axioms; the other six use only
`[propext, Classical.choice, Quot.sound]`. This is a model/control-flow result,
not an impossibility theorem for the shipped privacy experiment. It forbids
silently replacing every entropy outcome with a successful nonzero secret.
The host used the slot launcher with 6G/8G/no-swap/64-task caps. No existing
shared source/object was overwritten and no dependent replay was needed.

## Stage 2 — necessary failure transport

`ProverCommitEntropyJoin18.failure_mass_le_bad` proves a necessary condition
for a coupling which agrees outside a fixed event: any observable runtime
failure absent from the model must have mass no greater than that event.
The concrete finite `RawRand = Fin 16 → (Fin 3 → OracleAnswer)` represents
sixteen independent uniform 96-byte draws, with no OS errors. It is not a
claim that the OS actually has this law. The zero draw trace has positive
mass; thus `no_exact_success_coupling` rules out an *unconditional exact*
coupling from this sampler to an always-successful `SecP` sampler.

This does **not** rule out the requested whole-run coupling outside
`realBad`/`selectedBad`; their budgets may cover a failure transport. It also
does not establish any lower bound relevant to the privacy target. In
particular positive mass is not compared with the existing query-scan bound.
The missing entropy component must account for this branch rather than
claiming an error-free type conversion.

J8658 failed on a missing namespace opening. Changed-source J8659 passes all
five audits with standard axioms: exit 0, wall 1.89s, peak RSS 3,521,096 KiB,
swaps 0; revision `6352cfd55` plus exact source hash. Fixed launcher caps
unchanged. The dependency was the accepted J8657 object; no old shared object
was overwritten. All failure receipts are excluded from accepted evidence.

## Stage 3 — exact successful-draw symmetry

`ProverCommitEntropySymmetry18` constructs a bijection of raw 96-byte
candidates for *any* permutation of `SecP`: valid candidates are permuted and
invalid candidates stay fixed. `run_equivariant` transports the entire
bounded draw loop with the same draw-state history, cursor and OS failures.
`successful_law_equal` proves that every two successful secrets have exactly
the same mass under sixteen independent uniform raw draws. The failure
outcome remains present in the unconditioned law. No giant carrier is
enumerated. This supplies the mathematical symmetry needed for a conditional
success law; it does not supply an OS law or erase the failure probability.

J8660 failed on local rewrite normal forms and an unqualified helper;
changed-source J8661 passes all seven audits using only standard axioms:
exit 0, wall 2.64s, peak RSS 3,501,884 KiB, swaps 0, revision `0549f01af`
plus exact source hash. Two harmless no-op `change` lints remain in the
inverse proofs. Source dependencies J8657/J8659 are unchanged and reused.
Caps remain 6G/8G/no-swap/64 tasks; no old shared module is overwritten.

## Verbatim endpoint before

No specialization is claimed. This is the actual retained signature:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100
```

## Verbatim endpoint after

The source remains identical; the requested specialized deletion has not been proved.

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100
```

## Actual simulator and demonstrated extraction obstruction

D73.2 already documents `sim::sim_e`; it is present under `r1p-check`.
Therefore the requested ideal run cannot be described as having no source
simulator and silently substituted by the independent-coin model. Its four
coin streams hash a common 32-byte seed with the domain
`UNPROVED:R1:SIM:COIN`, attempt, stream and counter. `Coins::nonzero` loops
without the real entropy adapter's sixteen-draw cap. Transcript programming
uses a BTreeMap with duplicate/conflicting-entry checks, and
`programmed_hash` answers from the programmed table before falling back to
HOST_HASH. `Simulated.times` is diagnostic timing data; the FS-observation
contract would need to state its treatment rather than infer privacy for it.

The frozen source hash and exact attempted optimized command are in
`sim-charon-v1-inputs.json` and its receipt. Charon/cargo returns 0 in
41.464s, peak RSS 710,104 KiB, swaps 0, but the 83,500,874-byte LLBC has
`has_errors: true`. The launcher checks that flag and rejects it, exiting 1
before Aeneas. Diagnostics include mismatched transformed Iterator trait
clauses for Enumerate, BTreeMap::IntoIter, IterMut, ChunksExactMut and Zip.
The complete stderr and tool hashes are retained. The LLBC is retained only
on the host; its SHA-256 and size are committed, not its bytes. Caps were
6G/8G/no-swap/64 tasks, four jobs, release compilation; no simulator or dense
arithmetic was executed. `#print axioms`: N/A. The production `sim.rs` is
byte-identical to `c35b7b481`; the host workspace also contains the inherited
part-17 cfg-only harnesses, all separately hash-pinned.

This is a demonstrated **translation obstruction**, not an impossibility
proof for the simulator or the requested joins. No unchanged retry was run.
The next source deliverable is an owned simulator reference, starting with
its coin/programming-table transitions and Kani source equality; an accepted
extraction of that reference could then replace this failed direct route.
A proof for independent model coins does not close this source obligation.

## Source entropy gates and retained failures

The actual production generator is unchanged; only cfg(kani) harnesses are
appended in the isolated host copy. `source-binding.json` checks byte-exact
production prefixes against `c35b7b481`; the original host revision marker
was inherited from part 17 and is retained, not silently rewritten. Input
manifests hash the full instrumented source. No source-level regression or
SBF rebuild was needed for these proof-only additions.

Accepted `state_only_entropy::entropy18` gates (unwinding assertions enabled):

| Gate / receipt | Exact scope | Wall s | Peak RSS KiB | Exit | Swaps |
|---|---|---:|---:|---:|---:|
| os_failure / entropy-os-failure-v1 | immediate OS error class and exactly one 96-byte call | 16.523 | 602256 | 0 | 0 |
| first_success / entropy-first-success-v4 | arbitrary valid 96-byte draw, exact three returned blocks and one call | 46.681 | 989876 | 0 | 0 |

These do not prove the OS distribution or all sixteen mixed rejection/error
paths. OS filling is stubbed; source slicing, validity checks, construction
and drop code execute. The prefix/capacity gates from part 17 are not replayed.

First-success v1 and zero-exhaustion v1 were stopped for proof-shape review
at 543.798s/2,157,220 KiB and 368.973s/1,309,608 KiB. Both are excluded.
The harness's 96-byte copying/arbitrary generation was made explicit, so a
34-iteration default bound could replace the global 98 bound. First-success
v2 fails an enabled unwinding assertion in zeroize's 96-byte drop loop
(9.037s/920,228 KiB); it is excluded. V3 keeps 98 only for that exact loop,
but was stopped after 320.106s/1,754,152 KiB. V4 additionally sets the source
generator loop to two iterations under the valid-first-draw premise, with
unwinding assertions still proving no hidden later iteration; it passes.
No cap was raised and no unchanged source/configuration was rerun.

Zero-exhaustion v2 uses the explicit-byte harness, exact 98-step zeroize loop
and 17-step generator-loop bounds. It times out at 600.002s (exit 124), and
is excluded without another retry. The time wrapper reports 15,296 KiB peak
RSS for this interrupted process; its cgroup aggregate peak is preserved in
the receipt and must be used when reviewing the resource cost. This timeout
is not a source counterexample. Its full source/harness and stderr remain
available for a future symbolic/source-step replacement.

All Rust gates use 6G/8G/no-swap/64-task scopes and four compiler jobs with
the required linker flag. Time is in Kani compilation and bounded byte/control
verification, not unoptimized field elimination. `#print axioms`: N/A.


## Owned simulator coin transition and byte/ROM adapter

The failed full extraction is followed by the P6 route for one source
transition. `sim::coin_owned18` retains the seed/attempt/stream/counter
fields and takes the hash callback explicitly. Kani
`sim::simcoin18::coin_transition` compares it with the actual `Coins::coin`,
checks the five exact hash slices on both calls, and compares answer, next
counter and all retained fields. The answer and all fields are arbitrary;
the Kani source gate assumes `next < u64::MAX`. This is one transition,
not a proof of the nonzero rejection loop or its termination.

Kani: exit 0, wall 14.496s, peak RSS 474,432 KiB, swaps 0. Owned-reference
Charon: exit 0, 42.656s, 577,592 KiB, swaps 0, `has_errors=false`.
Aeneas: exit 0, 0.312s, 61,600 KiB, swaps 0. Both LLBC hash/size and raw
Lean text are retained; no LLBC bytes/binary are committed. Promotion only
narrows the root import, retaining every generated declaration/resource
option. All use the required caps and optimized extraction profile.

`AspisR1SimulatorCoin18.Types/Funs` compile in J8663/J8664 (each 1.39s;
2,503,104/2,517,832 KiB; exit 0; swaps 0). J8665 checks
`ProverCommitSimulatorCoin18.extracted_step` and `successful_step`: 1.32s,
2,515,388 KiB, exit 0, swaps 0, standard axioms. The reference extraction
preserves release-mode `wrapping_add`, including the exact callback frame;
this does not extend the Kani source gate to overflow inputs.

`ProverCommitSimulatorOracle18.source_frame` proves the concatenated
source hash slices match the model bytes. `indexed_injective` separates
8 attempts × 4 streams × any counter bound at most 2^64. The seed is fixed.
`coins_uniform` then derives the independent coordinate law from a uniform
finite random-oracle table. It is explicitly **not** a law for deterministic
HOST_HASH, nor a joint-history transport after previous oracle observations
or programming. It introduces no claim about freshness against an observer.

J8666 fails on a namespace and concrete finite-address elaboration; J8667
and J8669/J8670 expose remaining finite-enumeration instance normalization.
J8668 never launches (SSH transfer failure; its number is retired). The
replacement keeps address/answer instances symbolic and uses the existing
`mean_fintype_transport` theorem instead of comparing their enumerations
by reduction. No resource option or cap is raised. Changed-source J8671
passes all five audits: exit 0, 1.89s, 4,042,756 KiB, swaps 0, standard
axioms. Exact snapshots and dependency fingerprints distinguish all attempts.
After 17:00 the launcher correctly uses the global lock rather than slots.
No existing shared object or concurrent-worker source was overwritten.
