# R74: safe sampler reads and actual inner-loop step

Base revision: `b963532305dbe50cc0ce68a7c8158104f9353de7` (R73).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Exact proved boundary

`SamplerWordRead` proves that every word cursor below eight in a 32-byte block
has safe offset multiplication, end-offset addition, four-byte slicing,
slice-to-array conversion, unwrap, and cursor increment. The returned word
is exactly the runtime's `core.num.U32.from_le_bytes` of those four bytes.
There is no internal failure on that path. Every masked word is at most
2147483647, and rejecting equality with P makes accepted values canonical.

`SamplerInnerStep.factor` proves that the **actual generated inner-loop body**
equals the factored read and decision calculation. This is the source link;
the read helper is not merely an independently tested replacement. Further
theorems establish:

- Exhausted iteration returns the unchanged state, block, cursor and prior
  limb with `accepted = false`, without squeezing or reading.
- With an available attempt and cursor below eight, the actual body reads the
  exact four bytes, advances the cursor and accepts or rejects the masked word.
- At cursor eight it calls the actual squeeze, then reads word zero of the
  returned block and advances to cursor one. The resulting branch retains the
  new transcript state. Backend failure or divergence is preserved by the
  theorem's monadic expression, not excluded by a success premise.
- Acceptance returns the masked value; rejection continues with the supplied
  advanced range, state, block and cursor.

The retained code uses the runtime little-endian function directly. An
independent integer formula/retained sampler-model correspondence is **not**
yet proved. Nor does a one-step theorem establish the full bounded inner loop,
four-limb iteration, full oracle trace or a sampling distribution.

## Compilation and axioms qualification

Two leaves compile, with **14 theorem audits**. Eight use only standard Lean
axioms. Six additionally depend on the cached runtime's opaque
`core.fmt.Formatter : Type`, via `unwrap`, as already documented in R72.
Safe conversion now proves this path's unwrap receives `Ok`; it does not
erase that type dependency or prove a Rust formatting implementation.
No new axioms, admitted proofs or hiding assumptions are introduced. The
release audit is therefore **PASS_SCOPED**, not standard-axioms-only.

Lean `leanprover/lean4:v4.32.0`, cached NUC workspace, `-j1 -M4500`.
Actual cgroup limits: High 5 GiB, Max 7 GiB, SwapMax 0, TasksMax 128. One final
two-leaf replay reuses 324 targets; all 285 dependency pins are checked.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/SamplerWordRead` | 0 | 2.19 | 3,709,828 | 0 |
| `AspisV8R19/SamplerInnerStep` | 0 | 2.12 | 3,705,820 | 0 |

The base revision, exact source hashes, commands, axioms and resource records
are retained under `evidence/r74-inner-step`. The 44-artifact manifest also
retains failed focused elaborations: namespace qualification, explicit
monadic arithmetic types, normalization of a dependent offset, and monadic
factorization simplification. They are not release passes; the final logs
contain no `sorryAx`. No resource-limit increase or full dependency build.

## First remaining proposition

Prove actual eight-attempt inner-loop execution and the cursor invariant
across repeated rejections and rollover. Then prove the four-limb mutable
iteration and independent byte/integer/model-observer correspondence, before
composing the circle map and outer retries. Full shared-oracle chronology,
joint-view simulation, failures/retries/publication loss and pre-beta
quotient-pair extraction remain separate open obligations.

No runtime or protocol change, and no new CU measurement. Retained complete
CU is **1,495,663 / 1,497,050**; both actual 1M-cap runs still exhaust. Full
privacy and soundness are not established. No deployment or wallet operation.
