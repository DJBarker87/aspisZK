# R475–R478: 64-bit constructor and allocation-view correspondence

All four focused targets compiled successfully in the pinned Lean 4.32 cached
workspace, from revision `e3ef5fbbc50a1d9f1c88ed791f3b34fbc85c2202`.
No verifier source or security parameter changed. The genuine verifier results
remain 999,790 / 999,532 CU; benchmarks and unchanged regressions were not rerun.

## Proved boundary

- R475 proves that the explicit 64-bit word casts, NonNull zero guards, and
  wrapped multiply/add pointer offsets decode to R472/R432. Origin information
  is retained independently of the address. The offset theorem is universal
  over this fragment's heaps, pointers, and counts, retaining `none` and the
  zero-offset case without an allocation.
- R476 proves command and whole-program correspondence for the complete
  checked constructor interpreter. Every local, storage operation, branch,
  rejection, and early-return result is retained. It uses the same readonly
  constant interpreter as R472. Word metadata comparisons are expressed by
  equality of their natural values.
- R477 proves that backed pointers and in-bounds indices are representable
  without truncation, and that word offset followed by the fragment's read
  returns precisely the indexed slice-view cell. The existing allocation
  bounds supply all arithmetic bounds; no independent load-success premise
  is introduced.
- R478 composes the word interpreter with R474's selected syntactic constructor
  projection, including both branch arms. For every word input, its decoded
  result equals R472's checked constructor result. Positive input addresses
  further give the existing `newIter` result, retaining allocation rejection.

These are explicit interpreter/representation correspondences. They do not
establish native Rust/LLBC pointer semantics, certify the external JSON
projection generator, or derive the actual caller's reference validity,
allocation image, lifetime, aliasing permissions, or frame. They do not prove
the actual whole fold, freeze callback, privacy, or soundness.

## Focused evidence

| Target | Exit | Wall time | Peak Lean RSS (KiB) | Swaps | Axiom reports |
|---|---:|---:|---:|---:|---:|
| R475PointerWordRuntime.lean | 0 | 1.89 s | 2,557,072 | 0 | 13 |
| R476WordConstructorExecution.lean | 0 | 15.23 s | 2,565,052 | 0 | 2 |
| R477BackedPointerWordImage.lean | 0 | 1.13 s | 2,541,932 | 0 | 6 |
| R478SelectedWordConstructor.lean | 0 | 2.36 s | 2,543,196 | 0 | 6 |

All 27 complete `#print axioms` reports contain only `propext`,
`Classical.choice`, `Quot.sound`, or no axioms. None contains `sorryAx`.
Exact source snapshots, source/import/runner checksums, revision, commands,
exit status, full logs and reports are in
[evidence/r475-r478-word-constructor](evidence/r475-r478-word-constructor/).
Earlier failed elaborations are retained separately as superseded evidence,
including their failed axiom output; they are not verified results.

Jobs used `lake env lean -j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`,
`MemorySwapMax=0`, and `TasksMax=128`. RSS is GNU time's Lean-child measurement,
not the small Python wrapper's cgroup peak. Unchanged successful targets were
not rerun after promotion.

## First remaining proposition

Bind the actual selected callback's input reference and native pointer
operations to this checked word/allocation interpretation, with the actual
layout, provenance, memory-read, lifetime, and frame conditions derived rather
than assumed. Then bind Fun70's native loop and mutable closure return to the
existing error-preserving fold execution. The optional UB guard and its
failure tail, empty slices, one-past endpoints, and Domain inverse must remain
visible. Full freeze extension and callback chronology, universal joint mask
compatibility, whole-view simulation, shared-oracle laws and probability
losses, and the source-acceptance soundness bridge remain open.
