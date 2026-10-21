# S7 accepted-run join continuation

Branch: codex/cx-s7-join-20261021. Base: 6c520f134.

## Stage 1 — basis reference and emitted block

`S7JoinBasisIdentity.value_eq_natural` proves the total binary-factor
reference equals naturalLineValue for every width 2^n and bounded index;
`production_basis` specializes the actual 64 columns without enumeration.
`S7JoinBasisBlock.block_exact` proves all 256 cells of the actual emitted
basis-block result, including unchanged cells, with concrete frozen M31.mul.
No per-step result, backend law, or block-success premise is assumed.
The outer array-to-natural-value induction remains for the next stage.

Focused successful attempts: BasisIdentity-2 and BasisBlock-3. All four
axiom reports are subsets of propext/Classical.choice/Quot.sound. Receipts,
exact commands/import hashes/source revisions and time/RSS/swap measurements
are in manifest.json and the per-attempt directories. Failed development
attempts remain recorded and are excluded from accepted evidence.

The matching dV_frozen S7 consumer is the ClosedSum term in
D0TypedChecks.verify, reached through OraclePortStoredDecisionDraftC4.arithmetic.
There is no standalone source-defined query_values stage in dV_frozen.
A semantic reference theorem is not yet a frozen whole-cone refinement.

No shipped source, existing Lean module, S1–S6 cone, lean-candidate, sibling
S7/S8 cone or headline is modified. No ELF rebuild is triggered. No complete
frozen manifest replay or premise deletion is claimed.

## Stage 2 — resumed basis completion

`S7JoinProductionBasis.total_exact` now compiles (attempt 4). It proves
successful concrete initialization and all six emitted basis levels, with
each of the 64 output cells decoding to `naturalLineValue` for every input
word. No canonical-input or successful-output premise is required. The
previous WIP initialization failed on an unreduced `if True`; the replacement
uses `ite_true`. Failed attempts stay in the receipt history.

The pre-stop successful `S7JoinGeometry` and `S7JoinQueryReference` receipts
establish total stored-domain line inverses/nonzero denominators, query-node
identity, and exact agreement with dV's query values and basis. They do not
establish constructor table bytes, opening decoding, or query/TX membership.
