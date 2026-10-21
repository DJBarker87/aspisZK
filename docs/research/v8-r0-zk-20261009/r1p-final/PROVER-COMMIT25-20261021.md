# Prover commitment part 25

Base `87684ed0d`; branch `codex/cx-prover-commit25-20261021`.

Target not yet established. Updated incrementally after each verified stage.
No tracked shipped file or concurrent-owned module is changed.
The final user-assigned Env J range 7500–7699 is used, after checking receipts.

## Stage 1 — owned add-small reference

Kani `iterator_equals_indexed` proves the shipped iterator body equals the
retained extracted indexed reference: same boolean and every final digit,
for all canonical eight-digit arrays and all addends ≤257. These are the
existing arithmetic theorem's domain and cover both gamma increments.
Both function bodies are copied mechanically from their pinned inputs;
only visibility and module names differ. No production source changed.

The successful v3 gate has exit 0, wall 1.087 s, peak RSS 159892 KiB, swaps 0,
6G/8G/no swap/64-task scope, and exact pins in `addsmall-source-pins.json`.
No Lean compilation is involved in this Rust gate (`#print axioms`: N/A).
P6 remains the explicit Kani/Aeneas translation trust boundary.

v1 is a rejected CLI invocation (missing `-Z unstable-options`). v2 is an
excluded unwind failure in the implicit 32-byte memcmp used by array equality;
v3 checks all eight scalar equalities instead, retaining unwinding assertions.
The source loops and bound remain unchanged. All three receipts are retained.
This closes the source equality for the owned add-small reference; it does
not by itself identify every caller or install the complete scalar policies.

## Stage 2 — exact rejection product coupling

`ProverCommitProduct25.swapEquiv` swaps a nonzero model coin with the first
nonzero word of an independent tape, preserving both the rejected prefix and
unused suffix. `swap_involution` proves it is a bijection. `raw_marginal`
proves the reconstructed entire source tape is uniformly distributed;
`model_marginal` proves the unchanged model coin law. `first_swap` gives the
model answer outside precisely the original tape's all-zero exhaustion event.
`coupling` constructs both exact marginals without a supplied law premise;
`instances_marginal` lifts them to any finite number of searches.

J7502 passes all six audits with only [propext, Classical.choice, Quot.sound]:
exit 0, wall 1.92 s, peak 4037016 KiB, swaps 0. J7500/7501 are excluded
elaboration/simplification failures, retained with exact source snapshots.
This is a concrete rejection-component coupling, not yet the whole source
oracle/caller coupling or either deployed WholeRunJoin.

`ProverCommitProductRun25.runJoin` now constructs the deployed `RunJoin`
shape for the entire 24-search rejection component, an arbitrary finite
retained state, retained seed, and arbitrary continuation (which may return
state/history/decision). Its coupling space is literally
`((modelCoins × OracleAnswer) × Tape)`, not a functionally manufactured tape.
`source_marginal` proves the complete raw-tape/state/seed law;
`model_marginal` retains the independent original product exactly. Agreement
uses only the existing `failure` exception, with no extra bad event.
This component theorem has no supplied coupling or marginal premise.

J7504 passes: exit 0, wall 2.01 s, peak 4035268 KiB, swaps 0, all five audits
use the standard three axioms. J7503 is an excluded tuple/elaboration failure.
The actual shared-oracle address reconstruction and full shipped continuation
are not identified by this theorem; calling it a shipped WholeRunJoin would
be incorrect.

## Stage 3 — circle caller and nominal carriers

The pinned Charon/Aeneas kit extracts the owned `circle25::point` caller
with no external templates. Its policy parameter replaces only the circle
sampler; record validation, row-order errors, all three hash calls and the
advanced state remain extracted. Charon: exit 0, 32.404 s, 577348 KiB;
Aeneas: exit 0, 1.042 s, 111408 KiB; swaps 0, all caps 6G/8G/no swap/64 tasks.
The source is a host-only reference, not an edit to a shipped file.

`ProverCommitCircle25` installs the existing all-block/two-fallback sampler.
`sample_total` proves exact selected model coordinates for either row.
`first_caller` and `second_caller` identify its successful returned point and
entire advanced state from the extracted checked/block calls; they expose
those local calls as hypotheses and do not assert a whole-source join.
`wrapper_roundtrip`/`semantic_roundtrip` prove coefficient and semantic-state
nominal conversions without loss. J7535: exit 0, 2.29 s, peak 3968716 KiB,
swaps 0; all six axioms audits are standard-only (wrapper roundtrip: none).
J7532/7533 are excluded literal-match simplification failures; the final
proof closes the tiny literal match by `rfl`, not a larger reduction.
Types J7505 and Funs J7507 compile separately. Raw/promoted source hashes,
tool/source pins, resource receipts and the import-only port diff are under
`extraction/circle25` and `receipts/circle-policy25-v1-*`.

The source-level circle-policy equality and the semantic validator's nominal
execution transport still need composition; fixture equality is not promoted
to that universal source theorem.

## Stage 4 — owned scalar policies and the remaining source gate

The 23 retained scalar-owner modules are compiled into Env J from their
pinned sources, not by copying native objects. The exact import/source map,
raw sources, final port diffs and hashes are under `sampler-owners.json` and
`extraction/sampler-owners`. No existing shared predecessor object is
overwritten: each owner name was absent from Env J. One irrelevant
mask-Horner import was replaced by the identical small array-index proof in
`ProverCommitArrayIndex25` (J7508: only propext); this avoids an unrelated
mask proof replay. Four old monadic proof scripts received local elaboration
ports; their statements and generated arithmetic bodies are unchanged.

`ProverCommitPolicies25` now installs unconditional owned gamma, ordinary
and rho policies into the extracted suffix. `gamma_rank` proves every
block's exact nonzero field rank; `ordinary_total` proves every block's
ordinary field rank; `scalar_after_block` preserves the trace/allocation/cast
continuation and advanced state. **The query policy is still an explicit
parameter.** J7567: exit 0, wall 1.92 s, peak 3961104 KiB, swaps 0; all seven
audits standard-only. This is an owned-reference policy installation, not
yet unconditional frozen-source equivalence for the whole sampler family.

The add-small source gate passes, but the candidate additionally rewrites
`low_base_p_digits`. Its full arithmetic comparison times out at 600 s,
and the isolated division-pass comparison times out at 180 s; neither is
accepted. The full gate's cgroup peak is 1310396416 bytes (the killed
process-tree RSS is not captured by GNU time's parent statistic).
The replacement control gates pass (two harnesses; 2.489 s, 279588 KiB,
zero swap), comparing byte parsing, all ordered cell inputs, outputs and
retained state for arbitrary paired cell responses. They establish traversal
wiring only; arithmetic-cell instantiation/source composition remains open.
All receipts are retained, with no unchanged rerun or increased cap.

`block_transport` additionally proves the semantic-to-circle nominal
execution join for the actual three-read block method, including every
hash error/divergence and wrong-row rejection. J7541: exit 0, 2.41 s,
3972420 KiB, zero swap; all seven circle audits standard-only. Validator
nominal transport remains distinct. Exact shipped source prefixes used by
the extraction are checked in `circle-source-binding.json`.

J7506/J7561 are preflight import failures; no compiler launched. The query
closure's retained source/std/caller correspondence is explicitly open in
its original manifest, so importing its mathematical schedule would not
by itself close that source gate.

## Stage 5 — persistent source stream and finite-ROM product marginal

`ProverCommitPack25` proves that moving a rejected search's unused suffix
behind the following independent window is a bijection. Its cut is fixed
by the already-consumed prefix. `ProverCommitPackWindows25` handles unequal
window lengths; `ProverCommitStreamPack25` composes three windows and proves
the next source positions are exactly `used a` and `used a + used b`.
`source_stream_marginal` proves the whole 15-word source stream uniform from
three model nonzero coins times independent five-word fuel windows.
This does not leave unused five-word gaps after early successes.

J7566/7568/7570 pass, respectively: wall 2.16/1.99/2.24 s, peak
4044676/4041400/4046384 KiB, zero swap. Their 18 audits use only the standard
three axioms. J7564/7565/7569 are excluded parser/rewrite failures.

`ProverCommitProductOracle25.words_uniform` lifts this construction to all
eight attempts. `source_oracle_uniform` reconstructs the single finite source
oracle at the actual stream-3 byte coordinates, proving its complete uniform
marginal without an assumed source distribution. `source_at` identifies every
packed coordinate. `observer_history` transports complete ordered adaptive
histories, repeats and termination outside precisely the existing seedGuess
event. J7575 passes: exit 0, 2.19 s, 4043884 KiB, zero swap; five standard
axioms audits. J7571–7574 are excluded elaboration failures; the replacement
keeps a finite dictionary opaque and uses `mean_fintype_transport` explicitly,
preventing kernel normalization of incompatible decidable/Fintype dictionaries.
No resource or heartbeat/depth limit is raised. The dictionary linter warnings
concern this intentional opacity, not an assumed finiteness or a new axiom.

`ProverCommitProductCarrier25` supplies actual carrier equivalences from the
existing `Fin 8 → SecP` and `FuelJoin22.Tape` (24 × 5) to these inputs;
`source_words_uniform` preserves their exact laws. J7577 passes: exit 0,
1.92 s, peak 4044988 KiB, zero swap, standard axioms only. J7576 is an
excluded coordinate-elaboration failure. These are local source randomness
and observer laws; the full source continuation is not identified yet.

## Product coupling and endpoint

Not yet constructed. No refinement premise has been deleted.
