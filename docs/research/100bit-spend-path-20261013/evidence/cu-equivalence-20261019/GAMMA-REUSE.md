# Gamma-table reuse: source preparation and caller proofs

Production Rust remains frozen at
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. Candidate 1 is
`3ab4faf7f5b488a0c82720717656a0ebf4c46efa`; its claim and preparation
bodies are still byte-identical to the frozen tip. No Rust changes, protocol
changes or CU reruns accompany this proof checkpoint.

## Checked results

`CuSavingsGammaTable.source_success` consumes the complete emitted **new**
preparation, in both one-fold and two-fold branches. From actual source success
returning `(Ok p, g)`, it proves `powers 29 p.gamma = ok g`. There is no claim
factor, claim-success, power arithmetic, decoder-success or transcript-success
premise. The proof extracts the successful unchanged calls and follows the
actual returned constructor. Both old/new claim functions remain independent
universal parameters, so their equivalence is not smuggled into this theorem.

`CuSavingsGammaCaller.callers_eq` consumes that invariant to equate recomputing
the table after the new preparation with reusing its retained table. Its context
is arbitrary: accumulator allocation, observer callbacks, errors and divergence
can occur before or after consuming the table. This closes duplicate computation
elimination **after new preparation**, rather than asserting that old preparation
already equals new preparation.

`CuSavingsGammaPreparation.preparations_eq` compares the complete emitted old
and new preparation bodies after projecting away the scratch table, including
all errors and divergence. It has one explicit local obligation:

```
oldClaim(sem, y1, inactive, gamma, kappa)
  = do g <- powers(29, gamma); newClaim(sem, y1, inactive, g, kappa)
```

`CuSavingsGammaTransfer.callers_eq_of_claim_factor` composes both comparisons:
old preparation followed by recomputation equals new preparation followed by
retention, for arbitrary error/context functions. It exposes the same local
claim-factor premise and does not introduce a whole-verifier equivalence
premise. Discharging that premise from the actual helper source remains required.

## Source and extraction scope

`extract-cu-gamma.py --check` pins all 18 exact source cuts and the complete kit.
The shared View, Prepared, Verified and Error carriers are exact declarations,
checked against both candidate sides and the frozen production revision. The
only preparation-body adaptation is renaming the inherent `new` method identifier
so the paired complete bodies coexist over one nominal Prepared carrier. The
inverse rename reproduces the source bytes. Shared callees are explicit universal
parameters; typechecking stubs and the generated axiom template are not theorem
interpretations.

The successful preparation emission uses the existing producer that emitted the
reference model, SHA256
`4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5`,
with `-checks`, `-abort-on-error`, and no LLBC rewriting or compiler changes.
`Types.lean` is promoted byte-for-byte. `Funs.lean` differs only by adding
`variable [Boundaries]` at its namespace. `FunsExternal.lean` replaces the
uninterpreted axiom template with the explicit universal parameter class.

`check-gamma-evidence.py` additionally checks the exact claim delta: moving the
first power computation out and replacing the gamma parameter with the supplied
table leaves the entire claim suffix byte-identical. The candidate's complete
tx1_prepare bodies differ only by the scratch parameter/call argument; its tx1
bodies differ only by scratch initialization, argument passing and removal of the
duplicate call (plus removal of an unused `mut`). These are text/source binding
checks, **not a Rust semantics theorem**. The tx1 wrapper execution still needs
admission and consumption of the combined theorem.

`GAMMA-ARTIFACT-PINS.json` retains post-run hashes of both LLBC inputs and the
successful raw emitted files. No LLBC binary, ELF, object or shared library is
committed. Exact frontend commands/features and resource receipts are retained
under each attempt.

## Focused evidence

All Lean results use a 6 GiB high / 8 GiB maximum cgroup, swap disabled, with
one Lean job at a time and aggregate reservation checks. Each receipt includes
revision, command, features, source hashes, RSS, wall time, swap and axioms.

| Target | Accepted receipt | Wall seconds | Peak RSS KiB |
|---|---|---:|---:|
| AspisR1CuGamma/Types | cu-gamma-types-b | 2.606 | 2,633,500 |
| AspisR1CuGamma/FunsExternal | cu-gamma-externals-a | 2.404 | 2,613,116 |
| AspisR1CuGamma/Funs | cu-gamma-funs-a | 2.205 | 2,658,832 |
| CuSavingsGammaTable | cu-gamma-table-d | 2.005 | 2,652,948 |
| CuSavingsGammaCaller | cu-gamma-caller-a | 1.604 | 2,628,864 |
| CuSavingsGammaPreparation | cu-gamma-preparation-d | 2.005 | 2,645,920 |
| CuSavingsGammaTransfer | cu-gamma-transfer-a | 1.604 | 2,623,872 |

Every accepted target prints only `propext`, `Classical.choice`, `Quot.sound`
and uses zero process/cgroup swap. Failed proof attempts remain evidence of
failed attempts, not theorem results. No unchanged successful target was rerun
to suppress an unused-section-variable warning.

### Frontend diagnostics, not admitted source proofs

- `cu-gamma-charon-a`: full exact claims and preparations extracted, exit 0,
  0.401 seconds, 212,960 KiB RSS, no swap.
- `cu-gamma-aeneas-a`: isolated no-join frontend rejects returns inside nested
  loops in the complete claim; exit 2. No partial emission is admitted.
- `cu-gamma-charon-prepared-a`: same complete source kit with **both** claim
  helpers opaque; exit 0, 0.401 seconds, 206,036 KiB RSS, no swap.
- `cu-gamma-aeneas-prepared-a`: isolated frontend hits its context invariant
  at the unchanged folded-root unwrap; exit 2. Strict checks were retained.
- `cu-gamma-aeneas-prepared-b`: original reference producer succeeds on those
  full preparation bodies; exit 0, 1.403 seconds, 114,576 KiB RSS, no swap.
- `cu-gamma-aeneas-full-b`: original producer on the full claims fails with
  `Not_found` in `InterpReduceCollapse.collapse_ctx_following_sequence` during
  branch joining; exit 2, 1.403 seconds, 117,216 KiB RSS, no swap. This differs
  from the isolated frontend's nested-return limitation. No partial emission
  is admitted, and no compiler repair/expansion was started.

The empty local `cu-gamma-types-a` directory was a prelaunch authoring/staging
incident: a nonexistent optional translation.json was expected. No Lean job was
launched under that name, so it is not a result and has no invented metrics.

## Remaining obligations

1. Discharge the local claim-factor equation against the actual source under the
   existing reference boundary. Byte-identical suffixes alone are insufficient
   for a completed machine-source equivalence claim.
2. Consume the combined theorem in admitted tx1_prepare/tx1 source execution,
   preserving semantic verification, allocation and observer/error order. The
   retained scratch is ephemeral; serialization and checkpoint composition
   must follow from actual caller execution, not just matching types.
3. Compose the other retained candidates and the outer verifier/adapter, then
   transfer the original soundness and privacy results with no new unproved
   equivalence premise. Existing SDK/runtime and reference theorem premises
   remain explicit. No timing-privacy claim is made.

Candidate 1 and the full goal remain **in progress**. This checkpoint changes
proof source and evidence only. The preceding status-only goal turn was no
progress; this turn revalidated the current files and produced the checked
preparation/dataflow/caller theorems above.
