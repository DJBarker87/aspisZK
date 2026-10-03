# R496 captured align-to-offsets execution

The captured selected `core::slice::align_to_offsets::<u8,u32>` generated function now has a compiled execution theorem in the supplied Aeneas bounded `Slice U8` representation. For every such slice it returns `(q,r)` with `q.val = length / 4`, `r.val = length % 4`, `q.val * 4 + r.val = length`, and `r.val < 4`. Any returned pair has these properties; no modeled `Error` is reachable. Both nonzero guards and the original division, wrapping multiplication, and remainder sequence remain in the function.

## Focused verification

- Final target: `AspisV8R19/R496AlignOffsetsExecution.lean`.
- Source revision: `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`.
- Final source SHA-256: `8671eb46ac152cec738ee34722f8620af3c46670f534725289d31d91f6800f92`.
- Final run: `1791048695346913000`; exit 0; wall 1.09s; peak Lean-child RSS 2,534,804 KiB; swap 0.
- Pinned Lean 4.32, cached workspace; `lake env lean -j1 -M4500`; individual systemd limit MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128.
- Six complete axiom reports cover all three theorems, the generated helper, and its two compiler-evaluated SIZE constants. All list only `[propext, Classical.choice, Quot.sound]`.
- Focused generated Types: exit 0, wall 1.01s, RSS 2,531,984 KiB, swap 0. Funs: exit 0, wall 0.96s, RSS 2,527,856 KiB, swap 0.
- Primitive-name compatibility: exit 0, wall 1.00s, RSS 2,525,632 KiB, swap 0; all four reports list only `[propext]`. These definitions are exact specializations of supplied `UScalar.div/rem`, including their existing failure behavior.

## Exact source route

R488's compiler-evaluated constant capture pins the actual helper body and SIZE values 4 and 1. R490's selection and fail-closed literal-initializer adapter preserve every original function body, signature, and guard. R491 repairs the existing slice-metadata rewrite's argument arity for the captured monomorphized signature. R497 binds only the exact captured `core::slice::{[u8]}::len<u8>` name to the existing supplied `Slice.len` builtin; the former external axiom is absent. The source matcher diagnostic explains why a generic pattern failed.

Raw translator output is retained. Focused files change only imports to cached constituent library modules and the definitionally identical primitive-name compatibility module. The complete source, checksums, tool/library revisions, translation/build failures, successful logs, and axiom reports are saved in `evidence/r490-align-offsets-source/` and `evidence/r496-align-offsets-execution/`. No unchanged successful check was repeated.

## Proved boundary and first remaining proposition

This proves execution of the captured helper in the supplied bounded Slice representation. It does not establish native pointer allocation, address alignment, lifetime, reinterpretation, or the successful image of the whole parser. Those are separate source-to-memory obligations; the theorem adds no premises asserting them.

The first remaining proposition is that the actual selected `align_to` and parser branches return the ordered decoded cells with the correct length and canonicality, or their exact errors, from the caller's actual byte allocation. The native split/from-raw-parts/iterator/Vec operations and caller frame must be justified. R494/R495 expose more of this actual library code but are source captures only.

The complete callback/freeze chronology, universal joint C1/H1/G compatibility including p0/p2, full published-view simulator and shared-oracle probability losses, original quotient-pair extraction before beta, quadratic-fold connection, and optimized-acceptance implication remain open. End-to-end privacy and security are not claimed. Verifier source, 999,790 / 999,532 CU, and all security parameters remain unchanged.
