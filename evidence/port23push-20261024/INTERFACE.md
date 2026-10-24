# Exact claim and retained boundary

The installed interface is unchanged. Before and after this job:

```
Port3_NativeRowFrame.push b j q m =
  do let out ← S7Kani2OwnedPush.push_owned (toBW b) j (toK q) m
     ok (fromBW out)
```

No installed premise was removed or replaced. No query child or effect consumer
was installed. Allocation/new is absent from this local push cone and is not a
prerequisite introduced by this job.

## New complete-result outer frame

`Port23PUSH.push_complete` quantifies every explicit external interpretation
`ι : ArrayIntoIter`, BatchedWeights b, index:Usize, power:QM31 and basis:U32:

```
verifier.BatchedWeights.push ι b index power basis =
  do let row ← Vec.index (SliceIndexUsizeSlice (Array U64 4)) b.raw index
     let updated ← verifier.update_residue_row ι row power basis
       ((b.terms &&& 3) = 3)
     ok {b with raw := b.raw.set index updated}
```

`push_bad_index` derives `fail arrayOutOfBounds` when the index is invalid.
`push_success_frame` derives indexed read success, ACTUAL emitted update success,
and equality of the ENTIRE returned state with that single Vec.set.
`push_terms_length` derives unchanged terms and Vec length. These use the concrete
Aeneas Vec.index_mut setter interpretation, not an arbitrary callback setter.
The theorem cases on bounds internally; it assumes no index/canonical/overflow
restriction. Complete Result equality includes fail and div; it does not assert
native panic rollback or preservation/erasure of an oracle prefix.

Carriers: raw is Vec (Array U64 4), terms Usize; source power has two CM31 records
with two U32 fields each. Existing owned K uses two U32 pairs. The intended map
copies all four words and both BW fields. No canonicality is encoded by either
carrier, and none is silently imposed here. S7 owned push reads the row first,
computes terms&3, invokes `residue_owned`, then obtains a Vec setter. The new
normal form still invokes ACTUAL `update_residue_row`, not residue_owned.
The row loop equality (including all failures) is therefore NOT discharged.

## Actual extraction and ABI obstruction

Immutable 3166426e45 verifier.rs:204,216-220,230-245 and full field carriers are
included unchanged. Root→actual inherent push→actual update/accessors are in
ordered LLBC and emitted Lean; source-audit.json checks exact bodies and spans.
Charon and Aeneas both exit0. Their raw artifacts remain unchanged as evidence
text; the external axiom template was never imported or accepted.

The generated external template says:

```
into_iter : Array T N → Result (IterMut T × (IterMut T → Array T N))
```

But the actual emitted caller computes
`back : IterMut U64 → IterMut U64` and applies `into_iter_back back`.
The first smallest compile fails at this application. It cannot typecheck with
that template ABI. The explicit parameter in the NEW parametric module is:

```
ArrayIntoIter := Array U64 4 →
  Result (IterMut U64 × ((IterMut U64 → IterMut U64) → Array U64 4))
```

This before/after ABI change is explicit, not claimed to be a native association
or an unchanged generated module. The full emitted declaration bodies are
checked by `Port23PUSH_promote.py --check` after exactly this parameter threading.
It adds no equality premise and no trust field. Every theorem holds for ALL
such interpretations; no particular one is installed. Thus the outer frame
survives arbitrary external results, but the desired native producer does not
follow. lean-001 preserves the original type error. lean-003 preserves two
proof elaboration goals; their printed sorryAx is Lean error recovery, not an
accepted axiom. No authored sorry/admit/axiom was added to proof modules.

## Exact native/std/effect frontier

Pinned selected host source: array/mod.rs:376-378 delegates mutable array
IntoIterator to `self.iter_mut`; slice/mod.rs:1061-1063 calls IterMut::new;
slice/iter.rs:219ff constructs NonNull/end pointers. Iterator next is generated
by slice/iter/macros.rs:156ff, with the non-ZST U64 branch comparing end,
advancing ptr.add(1), and yielding the mutable reference. Vec.index_mut delegates
to slice indexing through DerefMut/as_mut_slice; usize SliceIndex.index_mut uses
intrinsic checked indexing. Rust's four scalar operations are U32→U64 casts,
checked extracted multiply/add, then mask/shift/add on flush. Range stepping and
Array.update are retained. The deferred fold loop back closures are retained,
not erased or replaced by an owned row.

std-source-graph*.json pins complete source files and selected exact bodies;
source-audit.json retains LLBC signatures and opaque leaves. The full Lean audit
prints concrete Vec read/set, IterMut.next, Slice.iter_mut and all new carriers,
loops and theorem statements. Existing Aeneas content primitives are reused;
this is not a new native/compiler/SDK/SBF identity gate.

D157 (LOG.md:8389ff) allows exactly documented pure collection interpretations,
excluding I/O/allocation-failure/concurrency/interior-mutation/hashing/unsafe
extensions. D189 (9001ff) supplies native AccountInfo↔heap and snapshot/runtime
allocator interpretation for S2. It does not itself bind this emitted mutable
array continuation ABI. No new TrustedStd field or primitive assumption was
installed here. A source-linked derivation of this exact array iterator/back
interpretation from the existing slice primitive is the next small obligation;
no blanket claim that new allocator trust is needed is made.

NoHash is NOT inferred from absence of Digest, Result equality, or a pure lift.
The native fixed primitive graph still needs its justified ordered effect and
panic/abort interpretation at this exact source site. The parametric ArrayIntoIter
ABI has no effect law; neither the frame theorem nor a favorable chosen instance
can supply one. Existing SDK interpretation may be reused only in its stated
scope. No source query allowance was removed.

Actual op6 arithmetic, four_dots, geometry, line/circle, accumulator updates,
trace and observer composition remain open. Port17's reached release observer
None invariant remains unchanged; no arbitrary Some inputs are rewritten and no
allObserver result is claimed. Both deployed targets remain not yet established.

## Validation and next work

New: two independently capped focused extractions, local source/frame/dependent
terms checks, one final complete-statement/axiom audit. Four successful Lean
invocations and two failed invocations, all retained. All successful theorem
axioms are subsets of propext/Classical.choice/Quot.sound. All measured swap0.
Own usage Lean6/13, extraction2/2, Kani0, standalone optimized Rust0, backend0,
manifest0. No assertion about other jobs' concurrent global usage.

Reused: warm Aeneas objects/content semantics, existing S7 statements and source
pins only. S7 arithmetic/Kani is neither rerun nor newly promoted to this source;
no old native evidence is a new artifact identity gate. Early lean-001..004 used
the inherited Port21 direct-import/source/tool hash receipt mechanism; final
dependent/audit runs additionally have explicit pre/go/post integrity snapshots.
These focused cached checks are not a coherent release replay or a native
primitive validation. No unchanged failed resource job was rerun.

Next deliverable: repair/justify the mutable-array continuation ABI using the
exact source delegation and existing slice interpretation, prove the symbolic
four-lane add-then-fold loop equivalent to owned scalar sequencing for all
Result outcomes, and only then compose a justified native effect producer into
the actual reached query child. This job stops at the concrete ABI/association
blocker rather than substituting the parametric outer frame for that producer.
