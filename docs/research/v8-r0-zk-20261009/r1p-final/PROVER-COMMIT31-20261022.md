# Prover commitment continuation 31 — publication owner

Source base: b5e845cb4 (inherited LOG D141). Branch:
`codex/cx-prover-commit31-20261022`. Stopped at a demonstrated extraction obstruction; target not established.

The native walk evidence from part 30 is reused. The next interface is the
ordered publication/retry owner, retaining the real tape/semantic/opening
contracts, then entropy/reservation, observable conversion and both run joins.
No refinement premise is removed by introducing an owned reference.

## Stage 1 — owned publication reference

Added cfg(kani)/cfg(aeneas_ref) `sim::owned31`: ordered consuming map snapshots,
conflict-retaining insertion, first-conflict merge, capped node publication,
and a copy of the actual simulator owner using these transitions. Production
control flow is unchanged. Five focused gates and all three frozen ELF
rebuilds completed; complete publication equivalence remains open.

BTreeMap stays TrustedStd: total lexicographic ordering of byte-vector keys and
numeric ordering of usize keys; unique keys; insert returns the prior value
and installs the new value; clone preserves entries; pop_first removes exactly
the minimum key; iter/into_iter visit each entry once in the same increasing
order; get/index return the unique value; len is entry count; entry/or_insert_with
retains a present value without invoking its closure and invokes the closure
exactly once before insertion when absent. No hash or
cryptographic property follows from these standard-library laws.

## Stage 2 — extraction diagnostics and focused source checks

The owned map loops remove both BTreeMap trait-clause errors. Charon v3 and
subsequent valid lowerings have `has_errors=false`; invalid v1/v2 LLBC is not
accepted evidence. Narrow opaque cuts retain the actual walk, tape, semantic,
opening, encoding, tree-programming and semantic-codec functions and errors.
They are obligations, not successful callbacks or discharged contracts.

Aeneas v3 rejects the native timing addition (`Invalid inputs for binop`).
The reference now retains those exact floating-point operations in opaque
instrumentation helpers. V4 requires the actual SecureCirclePoint ADT, and
v5 the actual R1PublicChallenges ADT; both type declarations are subsequently
included. V6/V7 hit `InterpMatchCtxs.ml:2739` in the mutable opening-cell loop.
Owned lane recursion advances extraction to the byte-publication loop (v8).
The current diagnostic is testing owned recursion for those bytes as well.
No successful Aeneas owner or new Lean theorem is claimed at this stage.

Accepted Kani gates: `publication31-wide_byte-v2` (3.561 s, 429800 KiB peak
RSS) and `publication31-cell_transition-v2` (7.197 s, 427072 KiB). Both exit 0,
zero swaps, with unwinding assertions enabled. The byte gate quantifies over
every canonical eight-limb value and an arbitrary byte position; the cell
gate over arbitrary 4×29 u32 arrays, update and observation coordinates.
The failed whole-array serializer check is an insufficient memcmp unwind
bound, not a serializer counterexample. Its replacement checks an arbitrary
byte without that irrelevant whole-array memcmp loop.

Initial map comparisons were stopped before pressure; whole-map equality,
then recursive BTreeMap clone, inflated the symbolic pointer state. Exact
stopped commands and scope peaks are retained. Changed focused harnesses
construct equal maps from identical inputs and compare selected lookup bytes;
these remain bounded caller checks. Map extensionality remains TrustedStd.
All scopes use 6G high / 8G max / zero swap / 64 tasks. Full commands, source
hashes, dependency fingerprints, exits, times, peaks and swap counts are in
`evidence/prover-commit31-20261022/rust-receipts.jsonl` beside exact source
snapshots. `#print axioms` is N/A for Rust; no Lean attempt has been consumed.

## Stage 3 — demonstrated owner extraction obstruction

V9 replaces both inner opening-byte loops with owned recursion. V10 also
replaces all three query traversals with index loops. Charon accepts these
sources with `has_errors=false`. Aeneas still exits 2 at
`sim_owned31.rs:151–159`, the first query's opening-value/publication loop,
with `Internal error, please file an issue` from
`interp/InterpMatchCtxs.ml:2739`, through the loop fixed-point equivalence
check. This is the same assertion after eliminating the inner loops and the
shared slice iterator. No generated Lean owner is accepted.

**Exact next interface:** an independently extracted, owned query-publication
transition/driver returning the updated ordered `opened` map, with ownership
of the base/ext coefficient vectors and query counter explicit, then its
composition into the attempt owner without the failing ambient loop-context
join. It must retain the actual encode_at contracts and cover duplicate
query replacement and serialization order. The current file is a proof-only
reference and extraction diagnostic, not a certified complete source owner.

The real entropy/reservation publication and source-output-to-ROMView/
ordered-observer conversion have not been discharged. Work stopped at the
requested demonstrated source-owner obstruction. Neither WholeRunJoin nor
`shippedProverExperiment` is constructed. `RustProverRefinement` stays
explicit. There is no deletion of a premise, no changed quantifier, carrier,
failure event or numerical budget, and no new cryptographic assumption.

The fixed-size capacity checks `oversized`, `exact`, `padded` each pass with
unwinding assertions (3.449/3.960/3.917 s, respectively; peak RSS
452704/452520/452396 KiB, zero swaps). They check arbitrary bytes in a
2-byte prefix and 2-byte node block at caps 1, 2, 3; they are bounded boundary
checks, not a universal proof of dynamic-length publication.

## Verbatim endpoint before/after

The endpoint module is byte-identical to `26b922be6`. Surrounding parameters
and notations are unchanged. These statements record no removal, not a
completed specialization. The full source modules and empty diff are retained
in the evidence `endpoint/` directory.

Before:

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))


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
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))


theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100

```

## Final validation and retained obligations

The exact final Rust reference and unchanged native simulator are committed
at `6372708025a3dad1abf4addbb47a7a74b09b02be`. Source snapshots, per-command
hashes and dependency fingerprints in `rust-receipts.jsonl` distinguish every
historical adapter. `final-audit.json` verifies all tested helper bodies are
byte-identical to the final reference, all other tracked crate/program input
hashes match this branch, and the native simulator text is unchanged apart
from its appended cfg-only module declaration.

There are **five accepted bounded Kani gates**, eight valid Charon lowerings,
and 24 diagnostics. There is **no accepted map-loop equivalence, no accepted
Aeneas owner and no new Lean theorem**. In particular, arbitrary map keys,
map order, complete conflict retention/early-exit transport, the new recursive
opening driver and its composition are not certified by these five gates.
The map checks were stopped before pressure and their receipt scope peaks
are retained. The literal two-key iterator check is also stopped, not green.
The insertion-summary Kani diagnostic exits 1 (cargo reports 101): the native
method has K, V and
allocator generic parameters while the monomorphic stub has none. It was not
worked around by an unsafe cast or by adding an assumption. This summary
would cover TrustedStd only; no opaque cryptographic helper is discharged.

Final owner v10 Charon: exit 0, 40.165 s, 579400 KiB peak RSS, zero swaps,
with `has_errors=false`; Aeneas: exit 2, 4.605 s, 649088 KiB, zero swaps, at
the opening-query loop's fixed-point context assertion. Full target, command,
wall time, peak RSS, swaps, source revision/overlays and tool hashes are in
the two receipts. This is a pinned frontend/source-shape obstruction, not
an impossibility proof for the simulator or its privacy theorem.

No Env J attempts were consumed. No Lean source or object was overwritten;
`#print axioms` is N/A because there is no new theorem. Part-30 J7871 and its
native-walk certificate are reused as inherited evidence, not rerun or
promoted to a whole-run proof. No unchanged full manifest, runtime suite or
arithmetic release gate was repeated. The full manifest preflight is not
green, so no formal release closure is claimed.

The shipped-file rule **was triggered and satisfied**. All three frozen SBF
builds ran in isolated 6G/8G/zero-swap/64-task scopes with four build jobs and
four linker threads, optimized, with time expected in incremental SBF
compilation/linking. They compare byte-for-byte against the original frozen
files (`cmp` exit 0), and match these SHA-256 values:

| ELF | SHA-256 | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| default verifier | dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34 | 0 | 2.984 | 203776 | 0 |
| devnet verifier | fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78 | 0 | 2.590 | 203904 | 0 |
| pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 0 | 0.416 | 100732 | 0 |

`frozen-elf-final-check.json` records sizes, exact commands and source hashes;
`frozen-source-inventory.json` checks all 493 tracked crate/program, Cargo and
.cargo files against that rebuilt source snapshot, with zero differences.
No ELF, LLBC, .olean, binary or archive is committed. All three build
receipts have `#print axioms: N/A` and the final source revision above.

The retained entropy boundary still includes immediate OS failure and the
sixteen-draw zero-block exhaustion event (`ProverCommitEntropy18.os_error`,
`zero_draws`; `ProverCommitEntropyJoin18.failure_mass_le_bad`). No OS law or
numeric OS-failure upper bound is supplied by those source contracts; its
full runtime event mass remains an obligation and is not set to zero. Under
the separately stated independent uniform raw-draw law, and with OS errors
absent in that mathematical raw carrier, the rejection probability per
96-byte draw is `1 - (1 - 2^-256)^3`, and sixteen rejected draws have that
quantity to the sixteenth power. This conditional arithmetic is not a new
source-law proof. Neither event has been silently absorbed into an unchanged
budget or replaced by always-successful nonzero secrets. The real durable
reservation transition remains open.

`Simulated.times` remains in the Rust return type. Its clock operations were
retained opaquely for extraction, but timing equality/privacy is not proved.
The requested source-output/ROMView/observer conversion must explicitly
settle timing treatment as well as proof bytes, tables, errors, query order,
retries and decision; no observation is silently projected away here.

Stages 1–2 are partial; stages 3–5 remain open. Zero refinement premises were
removed. **Target not yet established.** The exact next deliverable is the
owned opening-query publication driver stated in Stage 3, plus its native
source/Kani transition boundary, before retry-owner composition.

All work stayed in this assigned worktree and its isolated host directories.
No task wallet/key was created or deleted, no privacy-cost file was edited,
no other worktree or shared Lean object was changed, and no push/merge was
performed. All job processes in this job's host directories are finished;
source snapshots and caches are retained. No local target directory was
created.
