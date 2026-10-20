# Prover commitment continuation 5 — 2026-10-21

Branch `codex/cx-prover-commit5-20261021`, base `a7b7621d9`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit5-20261021/`.

## Stage 1: single-try verification and symbolic composition

The two timed-out full 16-try harnesses are not rerun. New proof-only
`mask_try_step` and `source_try_step` harnesses compare one carried-result
transition on arbitrary valid state (word slot 0 through 8, arbitrary seed,
counter and cached block). Success is absorbing; failure consumes exactly
one shipped `next_word` and classifies the candidate with the shipped try
expression. Both sides use the same retained memoised oracle, including
repeat lookups and possible collisions. The capacity/call budget is asserted
at two, not assumed. The post-state comparison includes every expander
field and the valid-slot invariant. `check-step-source.py` pins and checks
both source try bodies, their 16 limit and the normalization used by the
harness. The actual production sampler bodies are unchanged.

`ProverCommitSamplerComposition` proves early-return/carried-loop equality,
success absorption, and invariant-restricted composition for any loop length,
including 16. Env J 8158 passes, 1.49 seconds, 2,578,208 KiB peak RSS, zero
swaps. Its four theorems use no axioms. The local equality is a named
hypothesis: a Kani receipt is not silently installed as a Lean axiom.

Further stage receipts and the exact source frontier follow below.

## Stage 2: checked H1 quotient and completion

`ProverCommitTapeCompletion` splits the **actual** `Tape K F` into a
`SourceTape` quotient and `Padding`. Ignored coordinates are precisely H1
lane 1 at row 0 or a copy-active row. All other affine coordinates and all
eligible noise remain in the quotient. `completionEquiv` is a lossless
bijection `(SourceTape × Padding) ≃ Tape`; every full tape has one fibre.
`quotientFibreEquiv` identifies every quotient fibre with the same `Padding`
type. These are symbolic bijections; no tape enumeration or huge finite
reduction occurs. The dependent-row balance lemma handles the erased row
symbolically, and `h1_completion` proves padding choices cannot change H1.

`ProverCommitTapeMeasure` proves uniform product completion is uniform on
full tapes, uniform full-tape projection is uniform on the quotient, and
**any observable factoring through the quotient** has the same law under
an arbitrary representative (including zero fill). `applyAff_completion`
checks the entire affine trace operation, including ordinary mask columns,
G, H1 and D, against the actual definitions. This avoids claiming a
zero-filled *raw tape* is uniform. It proves uniformity only of the
observable that ignores the redundant coordinates.

Accepted attempts: 8162 (completion, exit 0, 1.89 seconds, 3,531,948 KiB,
zero swaps) and 8164 (measure/trace, exit 0, 2.09 seconds, 3,526,584 KiB,
zero swaps). All thirteen theorem audits use only `propext`,
`Classical.choice`, `Quot.sound`. Rejected drafts 8159–8161 and 8163 are
retained and excluded. Source SHA/dependency fingerprints and full outputs
are in `lean/`. The launcher snapshots this job's previous versions before
replacing its own shared objects; no peer-owned module is replaced.

This construction makes completion randomness explicit. It does not prove
that the shipped expander streams provide independent uniform `Padding`,
or identify a source decoder with a uniform quotient law. A quotient
privacy endpoint must transport every relevant observable, not merely
`applyAff`. Thus this stage does not install `R_commit_equal_fibres` for an
existing `Pr`, assume a cF, or silently change the existing protocol endpoint.
