# Prover commitment part 17 — ordered traversal and source boundaries

Base `47ccfa22c`; branch `codex/cx-prover-commit17-20261021`.

## Scope

The requested target is the shipped prover's `RustProverRefinement`, for both
real and ideal runs. Existing part-16 evidence is reused only in its original
scope. Its four accepted checks are one-value compaction, one-value rejection,
one-value expansion and node-slot offsets; they are not four full sections of
the proof serializer. No timed-out ordered-Vec harness will be rerun.

The concurrent worker owns SourceIdentification, RustRuntimeJoin and
PrivacyR1FinalRelease; those modules are not edited. No production source,
wallet, key, security target or frozen artifact is changed.

## Stage 1 — ordered section and per-element composition

`R1Z.ProverCommitTraversal17` proves arbitrary-length append induction,
ordered 10+12 projection before sorting, the fixed order header/transcript/
openings/nodes, four-callback equality composition, and the 57,607-byte length
from the explicit successful section lengths. The transcript phase includes
compact semantic, compact y1, inactive, round0, folded root, round1 and final.
No section callback is silently identified with Rust.

J8641 failed because `prefix` is reserved Lean syntax; it is excluded.
Changed-source J8642 passes: exit 0, wall 0.76s, peak RSS 1,409,788 KiB,
swaps 0; source revision `47ccfa22c` plus exact source snapshot hash. All
seven axiom audits are empty or `[propext]`. Each attempt uses the existing
slot launcher with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
No shared existing source/object was overwritten (only this new module's
failed source was replaced); no dependency replay was needed. Exact source,
dependency fingerprints and full audit lines are in the part-17 `lean/`.

Five replacement Kani checks pass (unwinding assertions enabled):

| Target in `compact::serialization17` | Wall s | Peak RSS KiB | Exit | Swaps |
|---|---:|---:|---:|---:|
| section_header | 2.593 | 365016 | 0 | 0 |
| section_transcript_cell | 3.726 | 379988 | 0 | 0 |
| section_opening_cell | 2.933 | 375168 | 0 | 0 |
| section_node_padding_cell | 3.061 | 377268 | 0 | 0 |
| ordered_element | 2.667 | 374404 | 0 | 0 |

These spend time in Kani compilation/bounded verification, with no dense
arithmetic; Kani's MIR profile is not a native debug arithmetic release gate.
Each uses 6G/8G/no-swap/64-task scopes, four compiler jobs and the prescribed
linker flag. Source revision `47ccfa22c`, exact instrumented source hashes,
commands and full output are in `rust-attempts.json`, `*-inputs.json` and
`receipts/`. Axioms: N/A (Kani, not Lean). The unchanged production source is
copied with only cfg(kani) harnesses appended in the isolated host workspace.

The header is complete. The transcript check is one compact 32-byte cell
(including both successful emission and unchanged-prefix rejection); the
opening check is one arbitrary lane's 4/16-byte slice; the node check is one
32-byte node plus one zero padding node. Their Vec prefix is three bytes.
The ordered check covers any batch, tree and legal ordinal of the real
22-element query array, compares the source map invocation to direct
indexing, and verifies one push onto a one-element prefix. It avoids all
prior timed-out Vec/sort formulations. The Lean append induction quantifies
all lengths at its List carrier, while the Rust Vec/List bridge still needs
certification. No large-prefix Rust claim follows from a small-prefix check.
`check-source.py --check` binds the exact source expressions and refuses a
changed source snapshot; it is a text-binding preflight, not an equivalence
proof. Sorting/dedup correctness, full semantic framing, opening lane order,
node multiproof traversal, and full Rust section callbacks remain open.
The prior four primitive codec results are reused without replay or a
claimed formal import into Lean.

## Remaining concrete execution boundary

`PrivacyR1HeadlineDeployed` still quantifies an independent `FSExperiments`.
Local codec equalities cannot construct its coupling, identify its randomness
law, or establish its success/abort oracle history. No premise removal is
claimed until those concrete obligations have been proved.

## Stage 2 — borrowed cells and all-length owned-state induction

`ProverCommitLoop17.run_related` proves an induction over an arbitrary input
list. A local transition relation gives equality of status and a relation of
all retained state; the induction preserves first error and iteration order.
The relation may include vectors, hash cursors and full oracle history. Its
local-step hypothesis is explicit, not silently instantiated for Rust.
J8646 failed on missing simplification in the error branch; changed J8648
passes with `[propext]`, exit 0, wall 0.64s, peak RSS 1,409,736 KiB, swaps 0,
revision `45a502067` plus exact source hash in the receipt.

The Kani one-iteration gates compare the literal borrowed cell body with the
owned collector (`remaining=1`) or a fresh-state padding-cell reference. An
unconstrained scalar result and successor state are explicit relational
inputs shared by both sides. Each callback asserts its exact input state;
every final seed/counter/block/word and scalar call count is checked. Both
success and scalar exhaustion are covered. These are **control-flow checks**,
not proofs of the scalar sampler or a probabilistic oracle law. They must be
composed with the existing scalar facts, not interpreted as verified stubs.
Resetting the call-record cursor between comparisons does not reset an oracle:
these checks make no oracle call and take one fixed scalar transition as input.

| `state_only_hiding::iteration17` target | Receipt | Wall s | Peak RSS KiB | Exit | Swaps |
|---|---|---:|---:|---:|---:|
| m31_push | m31-push-v1 | 13.546 | 746508 | 0 | 0 |
| qm31_push, fixed old zero | qm31-push-v1 | 11.498 | 748732 | 0 | 0 |
| padding_row, fixed old one | padding-row-v1 | 9.829 | 721048 | 0 | 0 |
| qm31_push, arbitrary old value | qm31-push-v2 | 10.377 | 748600 | 0 | 0 |
| padding_row, arbitrary old value | padding-row-v2 | 8.495 | 720852 | 0 | 0 |

The changed v2 gates strengthen their old contents; m31 is not rerun.
The push buffers have one old entry, so the bounded Rust result alone does
not establish arbitrary-capacity vector semantics. Padding quantifies its
row/dependent/predicate and verifies zero calls on skipped rows, one call on
taken rows, no write on scalar failure, and exact retained state. It compares
one cell rather than the full borrowed 1024-row loop. `run_related` proves
all-length transport **if** the concrete source transitions instantiate its
local relation. The existing Aeneas Vec push specification and part-16 prefix
induction remain reusable but do not manufacture that source instantiation.

All Kani runs use 6G/8G/no-swap/64-task scopes, four compiler jobs and the
prescribed linker flag; time is in compilation and bounded verification.
`#print axioms`: N/A. Exact revision/instrumented source hashes and commands
are in `rust-attempts.json`, the input manifests and receipts. The v1/v2
harnesses are retained separately. No unchanged timed-out gate was rerun.

## Stage 3 — owned outer assembly extraction

`assemble_owned17` is a new proof-only Rust reference taking preallocated
owned buffers and a retained state. Its order is c1, ten mask-only columns,
g collection, g balancing, padding collection, padding balancing, final
returned material and nonce. Each call binds fresh owned values and state;
all errors return the exact state reached and suppress partial material.
It starts **after** nonce reservation, seed derivation and allocation. It
neither replaces nor proves equality of the shipped outer borrowed builder.

Charon `assembly-charon-v1` passes in optimized release mode: exit 0,
24.309s, peak RSS 673664 KiB, swaps 0. Aeneas `assembly-aeneas-v1` passes:
exit 0, 0.800s, peak RSS 102080 KiB, swaps 0. Both use the fixed host caps.
No failed borrowed-loop extraction is rerun. The LLBC is recorded by hash
and size only; raw generated Lean text, tool hashes, input source hashes and
receipts are retained in the part-17 evidence directory.

`AspisR1ProverAssembly17.{Types,Funs}` are the promoted extraction. The
promotion script makes only explicit port compatibility edits: narrow the
root import to Std/RustAttributes/Data.Discriminant, and replace the
unsupported generated discriminant attribute with the same five-constructor
explicit discriminant instance used by Material14. Generated resource
options remain exactly generated. No new handwritten resource option exists.
J8645 fails on the unsupported attribute; J8647 exposes the missing narrow
Discriminant import. Changed J8649 (Types) and J8650 (Funs) pass: respectively
1.29s/2528576 KiB and 1.63s/2546052 KiB; exit 0, swaps 0. No old shared module
was changed. The failed versions are excluded and retained in the receipts.

`ProverCommitAssembly17.extracted_stages` connects the extracted outer Rust
function to the six named monadic stages. `first_stage_error` preserves the
advanced state on rejection. Recursive collectors and balancers stay named;
no large recurrence is normalized. J8651–8653 expose only differing match
normal forms (Unit pattern and constructor branch order), not a counterexample.
Changed J8654 aligns those small matches and passes both audits using only
`[propext, Classical.choice, Quot.sound]`: exit 0, wall 1.25s, peak RSS
2525796 KiB, swaps 0, revision `45a502067` plus the exact source snapshot hash.

This closes the extraction-friendly **owned outer reference** composition.
It does not close borrowed-source all-length iteration, the extra clones /
allocation behavior, nonce/entropy/zeroization boundaries, or the nominal
type transport from the new extraction back to Material14/Returned16. No
source-to-model security premise is removed by this stage.

## Stage 4 — whole-run obstruction and retained endpoint

`ProverCommitRuntimeObstruction17.no_unrestricted_endpoint` constructs an
independently supplied experiment with inhabited singleton randomness
carriers, identical disclosed views, and a public oracle-history-length bit
that differs between real and ideal runs. Its distinguishing advantage is
exactly one. Therefore deleting the refinement premise while leaving the
existing `rust : FSExperiments` quantification unrestricted is false for
any epsilon below one. This is a countermodel to that proposed inference,
**not an attack on the shipped prover**, and not a proof that a concrete
shipped adapter cannot be verified.

J8643 initially misses the explicit Fintype instances for the defined
carriers. Changed J8644 passes the countermodel's axiom audit with only
`[propext, Classical.choice, Quot.sound]`: exit 0, wall 1.58s, peak RSS
3489488 KiB, swaps 0, revision `9cb63237e` plus exact source snapshot hash.
All host caps and launcher slot locks are unchanged.

**Target not yet established.** No new deployed endpoint or strict weakening
is claimed. No premise is removed, added, repackaged, or renamed in the
existing endpoint. The before/after source is byte-identical; `endpoint.diff`
is deliberately empty and `endpoint-status.json` records both hashes.
Neither a whole-run real coupling nor a whole-run ideal coupling has been
constructed. The countermodel means local helper checks cannot justify an
unrestricted premise deletion; it does not turn unfinished concrete runtime
work into a proved impossibility.

Remaining concrete deliverables are:

1. Instantiate an independent shipped experiment from its exact input/entropy
   carriers, builder/checker/retry behavior, visible errors, ordered proof
   bytes, and retained shared-oracle history. The existing endpoint has no
   such concrete instance. No concurrent-worker module was touched to obtain
   one by assumption.
2. Supply arbitrary-length borrowed-Vec/source iteration identification and
   transport the new owned extraction to the old material/model types.
   Verify the full semantic framing, source sort/dedup and multiproof traversal,
   rather than promoting the emission-cell checks to those claims.
3. Establish exact retained transcript recovery on success and abort, then
   instantiate both existing WholeRunJoin obligations (real and ideal), with
   the fixed bad events and the same randomness law. OS entropy, nonce-store
   reservation, allocation/disposal and sampler/model alignment remain explicit
   implementation boundaries, not new cryptographic assumptions.

The next narrow source deliverable is a complete serializer source model,
including its semantic-row and multiproof-node iterators, with arbitrary
prefix Vec semantics and Rust-to-List transport. The new cell checks and
all-length induction can be reused there. A model alias named “shipped”
would not supply either missing WholeRunJoin and is not introduced.

## Verbatim endpoint before

The following exact declaration span includes the refinement definition and
full theorem signature; its unchanged surrounding local notations and types
are in `endpoint-before.lean.txt`.

```lean
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
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100
```

## Verbatim endpoint after

No new endpoint is substituted. The exact same declaration span remains:

```lean
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
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) < 1 / 2^100
```

## Final cached audit and evidence validation

J8655 targets `R1Z/ProverCommit17Audit.lean`, after all adopted Lean sources
are frozen. It imports the new traversal, loop, owned assembly and runtime
countermodel alongside the unchanged deployed endpoint. Exit 0, wall 1.95s,
peak RSS 4093644 KiB, swaps 0, source revision `dd0211c96` plus the exact audit
source SHA-256 and imported-object fingerprints in its receipt. All twelve
`#print axioms` reports are empty or subsets of
`[propext, Classical.choice, Quot.sound]`. No recursive callee was unfolded or
unchanged dependency rebuilt. This is one cached composition/axioms audit;
**no full frozen release-manifest replay or shipped-prover release result is
claimed**, because neither concrete WholeRunJoin instance exists yet.

`harness/final-audit.py` passes source/snapshot hash checks, all accepted and
excluded Lean statuses, full allowed-axiom parsing, the ten successful Kani
receipts, both extraction receipts, ported-source hashes, literal source
bindings, exact v1/v2 instrumentation reconstruction, fixed resource limits,
and unchanged endpoint/production sources. `final-audit.json` records its
result. Receipt error extraction was corrected to recognize Lean diagnostic
syntax instead of the substring “error” in a successful theorem name such as
`first_stage_error`; raw output, compiler status and proof results are unchanged.
No proof or build is rerun for that metadata correction.

Evidence is under
`docs/research/100bit-spend-path-20261013/evidence/prover-commit17-20261021/`.
No ELF, .olean, LLBC binary, archive, wallet or task key is committed. There
is no local target directory. No push, merge, production source change,
concurrent-worker edit, resource-cap increase, or security-target change was
made. Attempts 8641–8655 are used; next assigned number is **8656** after
checking host receipts. All earlier timed-out ordered-Vec jobs remain excluded.
