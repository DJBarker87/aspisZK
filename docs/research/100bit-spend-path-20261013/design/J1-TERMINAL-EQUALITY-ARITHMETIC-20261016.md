# Checked terminal equality loop, arithmetic and fold order

Seven further focused Lean 4.32 targets pass. The actual extracted equality
function now returns a canonical QM31 value whose decoded value is the
existing `R0P.SemSource.eqValue` product. Its inputs are two fixed arrays of
ten canonical QM31 values; read success, loop termination and checked index
increment are proved internally.

The [independent evidence review](../evidence/terminal-equality-arithmetic-20261016/root-review.json)
checks 302 checksums, seven selected source/receipt/output chains, thirteen
raw standard-only axiom reports, and the represented dependency edges.
Twenty-three failed attempts are retained and excluded from proof claims.
`EqualityValueSlice` has no axiom reports and counts only as a checked compile.
The archive also contains a second successful product receipt, without
double-counting it as another target.

## Exact scope

`EqualityValueLoop.equality_value_success` is an execution theorem for the
copied generated function, not merely an identity for a hand-written model.
Its only input conditions are canonicality of the two fixed arrays. The
four function declaration blocks and closure type alias are copied exactly
from translation G, apart from surrounding whitespace and module framing.
The old shared selected-mask `Funs` and `Types` imports have separate pins;
they are not mislabeled as the full G output. Translation to upstream Rust
and whole-program compiler preservation remain distinct obligations.

`ExtractedMaskTerminalArithmetic.terminal_scalar_calls` proves the eight
successive generated field-operation calls and decodes their result as
`q * composition + mu * h1 + mu * mu * ((1 - active) * h1)`. It assumes
canonical component inputs. It does not yet prove the enclosing
`terminal_parts` wrapper or identify the component producers.

`ExtractedMaskTerminalHorner.composeGroups_eq_lane_sum` proves that reverse
folding 24 semantic entries, then four Poseidon entries, starting from the
copy residual gives the intended 29-coefficient polynomial. Its hypotheses
explicitly require the two arrays and seed to match those lane coefficients.
This is pure fold algebra; actual extracted fold-loop execution is subsequent
work. It must not be counted as discharging the array-producer hypotheses.

## Reuse and provenance

The proofs reuse checked QM31 arithmetic, canonicality, fixed-array indexing,
and the existing semantic equality product. The imported `R0P.SemDecision`
object is exactly the output of the already published queue144 target 067:
source `cf8c98e1bf6d5da3a2e725efd3790c4efc7e75fc32b0c650c310d875bf1f8971`,
object `04fac0e5384ce0fd263ca7794687e4187c685fec9ffde01ec1cb3a43df48c64c`.
The original successful receipt and snapshot reconcile the null source
fields in the new import receipts; those receipts were not rewritten.

Three historical `SourceMixing` declaration blocks are reused verbatim in
`TerminalHornerCore`, with new imports and namespace framing. The final
Horner targets do not import the old broad `SourceMixing` object. A scratch
broad-import attempt hit Lean's memory threshold and exited 134; its source,
6 GiB cap, memory exception and receipt remain archived. It was replaced by
the minimal declaration slice, with no unchanged larger-cap retry.

## Focused NUC checks

Every selected target exited zero, with zero reported process swaps.
Each job used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`,
`TasksMax=128`, Lean `-j1 -M5000 -DElab.async=false`, and timeout 300 seconds.
Times below are GNU time's wall times, not total development time.

| Target | Wall time | Peak RSS (KiB) | Axiom reports |
|---|---:|---:|---:|
| EqualityValueSlice | 1.21 s | 2,605,460 | 0 |
| EqualityValueAdapter | 1.48 s | 2,993,476 | 3 |
| EqualityValueProduct | 1.93 s | 4,017,380 | 1 |
| EqualityValueLoop | 2.76 s | 4,045,076 | 2 |
| ExtractedMaskTerminalArithmetic | 1.51 s | 2,992,264 | 1 |
| TerminalHornerCore | 1.00 s | 2,073,064 | 2 |
| ExtractedMaskTerminalHorner | 1.11 s | 2,080,116 | 4 |

The exact new source hashes are recorded separately from the preserved
workspace base revision `b40d1cfffadbdf967f84cca23ea4e7f1553d564f`.
No full manifest replay or dependency rebuild was performed.

The complete terminal source/model relation, actual accepted-verifier
composition, efficient extraction, privacy, Fiat–Shamir composition and
runtime release remain open. This checkpoint makes no new CU measurement or
complete 100-bit security claim.
