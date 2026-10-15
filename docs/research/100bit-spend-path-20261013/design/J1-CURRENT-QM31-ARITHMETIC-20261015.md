# Current extracted QM31 arithmetic checkpoint

The current production field arithmetic now has checked modular-word contracts
for canonical addition/subtraction and CM31/QM31 multiplication. This removes
an arithmetic sub-obligation from the Rust-to-model work; it does not establish
that an accepted verifier execution satisfies the terminal theorem's premises.

The standalone extraction copies the complete current `field.rs` and
`field/wide_exact.rs` unchanged from revision `ccb6f8463`. Its new probe wrapper
calls `QM31::add` and `QM31::mul`, producing 13 nonopaque function definitions.
The scope disables default features and `r0-op-count`, `r0-r91-audit`, and
`r0-e4-reference`. Matching the selected verifier's exact feature configuration,
callers, and built artifact remains a separate obligation.

## Existing work reused

`AspisV8R17.RawReducerNat` is reused byte-for-byte. The M31, CM31 and QM31
composition proofs follow the retained V8 R17 routes. Nine current generated
function bodies match the corresponding old generated bodies after namespace
and whitespace normalization; this comparison is evidence, not a semantic
proof. The old runtime projection cannot safely be imported alongside the real
Aeneas runtime because it redeclares runtime types. The new proofs therefore
use the actual cached Aeneas runtime and freshly generated functions.

The checked reducer accepts every stored U64 and returns its canonical residue.
Current M31 multiplication accepts every pair of stored U32 values and returns
their product modulo P. Addition/subtraction and tower multiplication retain
explicit canonical-input premises and prove canonical output. The final QM31
theorem identifies the four result words with the retained modular formula.
Its interpretation in the exact mathematical tower is the next bridge.

## Validation

The [root audit](../evidence/current-qm31-arithmetic-lead-review-20261015.json)
checks nine successful focused targets and 33 axiom reports, all using only
`propext`, `Classical.choice`, and `Quot.sound`. Generated Types/Funs contain
no axiom reports; they are counted as compilation targets only. All jobs used
Lean 4.31.0 and cached dependencies. Peak sampled aggregate process RSS was
2,797,424 KiB; all captured process swap counts were zero. Exact commands,
source/object/tool hashes and resources are retained in the
[bundle](../evidence/current-qm31-arithmetic-20261015/README.md).

Both failed first multiplication attempts remain in the bundle and are
excluded from successful results. CM31 needed an explicit intermediate product
bound; QM31 needed intermediate-word rewrites before unfolding the word map.
Neither repair changed premises. No full regression or dependency rebuild was
run. The bundle's preparation README calls it unsealed; the separate root audit
pins the reviewed snapshot without rewriting its preparation history.

## Still open

- Exact-field decoding of these current operation results.
- Caller canonicality, semantic loop composition, selected-mask prepared
  multiplication and terminal evaluator correspondence.
- Acceptance-to-terminal conditions, commitment compiler, sampler/source and
  admitted runtime correspondence, efficient extraction and privacy.

The transparent two-transaction route remains a candidate with measured runtime
evidence and partial formal proofs. This checkpoint does not claim the complete
100-bit per-attempt private-spend theorem or a release-ready artifact.
