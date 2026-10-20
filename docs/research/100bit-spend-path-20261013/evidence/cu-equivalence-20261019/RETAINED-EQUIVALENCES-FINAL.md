# Retained CU equivalences: completed source transfer ledger

All ten retained source replacements are checked: **1, 2, 3, 4, 5, 6, 7, 10, 12 and 14**. Their remaining input-provenance and source-caller links are closed. Reference: `f458169f705f25b04e1e29546c621e4665e0f64c`. Frozen production Rust: `39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. Production Rust was not changed by this proof work.

| Source replacement family | Checked consuming result |
|---|---|
| Gamma reuse, actual claim, delayed/canonical/prefix dots and rho stages (1/4/5/10/12) | `CuSavingsRetainedQueryPrefixGammaRho.source_tx1_equivalence`: actual original Gamma/claim/rho/query tx1 to retained Gamma/claim/rho/query tx1. `CuSavingsRetainedQueryPrefixTx2.tx2_equivalence` and `.tx2_authenticated_equivalence` bind real kernels through complete resumed query stages. |
| S2, remaining canonical pairing consumers and Libra (3/5/14) | `CuSavingsRetainedFinishDotContexts.Prepared.source_equivalence` and `.Resumed.source_equivalence`: execute complete preparation/resume, derive the inputs internally, then consume the actual finish-relation dictionary and fixed source client frames. |
| Geometry reuse (7) | `CuSavingsGeometryStage.source_caller_equivalence` and `CuSavingsGeometrySingle.source_public_query_context`: actual builder/cache lineage, checked counter advancement and all four source caller ranges. |
| Diagnostic profiling removal (2) | `CuSavingsProfilingCandidate2.all_observations_eq`: source-factorized observer and SDK diagnostic projection, retaining application effects and the sufficient-reference-resource boundary. |
| Public-statement decoder reuse (6) | `CuSavingsPublicDecodeCallsite.observations_eq`: actual decoder/selection and argument order, original bytes and complete source call-site context. |

The claim now uses the actual six-point and seven-part source loops, strict source scalar selector, sampled gamma and actual powers before claim execution. All five canonical-dot consumer families are covered: claim; query tail; ordinary field-stream pairing; shared partials/high; final enumeration. The complete endpoints derive their required invariants internally; they do not assume canonicality, successful child execution, an arithmetic law or the desired candidate equivalence. Older component results with explicit premises remain historical component contracts, not the unconditional whole-caller result.

The exact ten KEEP patches reconstruct the entire frozen `crates` and `programs` subtrees. Four DROP/revert pairs restore their exact predecessors; no source-changing revision is omitted. The source ledger composes checked contextual replacements at their exact source sites. It is not a claim that one monolithic extraction of the entire final program was compiled into a single theorem. The joint file checks coherent imports and audits the consuming theorem axioms; imports alone are not the composition argument.

## Validation and boundaries

- `TEN-COMPONENT-FINAL-AUDIT.json`: all ten candidate checks, plus the source-origin audit, pass. The incorrect geometry audit flag was corrected once; its diagnostic is retained.
- `RETAINED-COMPOSITION-RELEASE-AUDIT.json`: all ten additional composition/input-binding checkers pass. CLI diagnostic attempts are retained separately; only failed argument checks were repeated.
- `retained-closure-final-b/receipt.json`: final joint Lean checkpoint passes, **4.008 seconds, 3,878,196 KiB peak RSS, zero swap**. Exact command, source revision/hash, feature set, object/import hashes and all `#print axioms` outputs are retained. The first checkpoint lacked the pinned semantic-finish cache overlay; its diagnostic is retained.
- Axioms are the existing standard three (`propext`, `Classical.choice`, `Quot.sound`), plus the inherited `core.fmt.Formatter` **Type-valued** runtime boundary where present. No `sorryAx`, native-decision axiom or candidate-equivalence axiom is introduced.
- `RETAINED-OBSERVATION-FRAMES.json` pins identical View/Prepared encoding, checkpoint/resume, challenge-sampling prefix, cryptographic query prefix and settlement event source. Changed arithmetic files contain no cryptographic calls. The existing expanded query-prefix trace theorem supplies the loop schedule; ordinary Result equality alone is not presented as an oracle-trace theorem.

The established Rust/Charon/Aeneas/compiler, ownership, library/runtime and sufficient-resource assumptions remain explicit. Gamma's narrow immutable-prefix interpretation and resume's fixed sequential array-fill interpretation are audited source-fission boundaries; failed direct frontend attempts are not counted as successful extraction. The original 64-bit/sufficient-heap and authentic-checkpoint premises remain. This work supplies source-equivalence transfer, not a new machine-code correctness or unconditional soundness/privacy theorem; the reference security theorem's existing premises still apply.

No unchanged SBF/runtime/codec suite was repeated for Lean-only changes. The pinned build's existing six-fixture measurements remain **1,199,687 CU maximum stage 1** and **1,188,496 CU maximum Pool settlement**, both below 1.2M. These are saved-fixture measurements, not a universal CU bound. See [the frozen CU report](../cu-savings-20261019/FINAL-REPORT.md).
