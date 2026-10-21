# Inner order draft — 21 October 2026

Unmerged draft on `codex/cx-inner-order-draft-20261021`. No approval of the
oracle port, no shipped change, and no premise removal is claimed.

## Stage 1: independent source-shaped slot

`OraclePortInnerOrderFrozen.lean` defines sorted leaf hashing with immediate
digest duplicate rejection, index-only sibling counting, per-slot capacity
and zero padding checks, binary level-order parent hashing with consecutive
sibling consumption, and the final index/root/remaining-byte comparison.
The live prefixes of the scratch arrays are represented by lists. Each group
is read before its parent is appended to the next prefix; no oracle query is
introduced by that representation change. `runLevels` is recursive on height;
`levels_step` exposes one level without evaluating a height-18 tree.

This is an independently written source model, not a proved extraction join.
`slotTail` rejects a short slot to totalize the helper outside the upstream
fixed-size proof invariant; Rust's direct slot slicing requires that invariant.
Source citations are in the module. Receipts are under
`evidence/inner-order-draft-20261021/`; private compiled objects are not committed.

## Stage 2: acceptance equivalence check

`OraclePortInnerOrderCounterexample.acceptance_counterexample` compiles:

```lean
(eval H (verifySlot_frozen ⟨badWire,[]⟩ zeroQueries 0 1)).2 ≠
  (eval H (OraclePortBatchDraft.verifySlot ⟨badWire,[]⟩ zeroQueries 0 1)).2
```

Here H answers zero to every query, all ten indices are zero, and slot 1 is
fully present with all bytes equal to one. Existing `verifySlot` accepts:
the symbolic occupied tree is one spine, every hash answer is zero, all
duplicate digests agree, and the empty semantic list makes the kind-1 root
zero. Frozen hashing also merges to one index; `count_singleton_zero` proves
`nodeCount h [0] = h` by induction. The count at height 18 is therefore 18,
and the all-one padding is rejected. No height-18 tree is evaluated and no
large byte list is normalized: `drop_replicate`/`take_replicate` and a head
comparison prove the padding failure symbolically.

This refutes the requested *unconditional helper* equivalence. It does not
refute equivalence on parser-reachable inputs satisfying `Padding`, or full
`dV_sc` verdict equivalence: that decision already rejects bad global padding.
The witness is intentionally a raw `Parsed` value, not a parser reachability
certificate. The helper theorem as requested quantifies over every input.
The counterexample is not based on short-slice totalization.

Attempt 1 had three corrected elaboration issues (find? reduction, the sort
proof, and an ambiguous Byte). Attempt 2 exits 0; every theorem has a standard
axiom audit. Failed compiler-recovery sorryAx reports are retained only in
the failed receipt and are not accepted evidence.

## Stage 3: independent rejecting-path accounting

`OraclePortInnerOrderRejectLog.rejecting_log` proves the counterexample's
complete evaluation: the ten leaf reads, in ascending source position order,
then false. `padding_stops` proves the continuation itself is `.done false`;
no parent query is issued. `rejecting_log_length` is exactly 10, hence the
witness's log is below 1161. This is a witness-specific result, not a proof
of the requested universal rejecting verifier budget.

The model must adopt the frozen behaviour: hash sorted leaves and reject a
bad duplicate immediately; then check this slot's node count and zero padding;
only then hash its parents level by level. The existing global padding guard
must be moved into the slot continuation for all-path source-order fidelity.
Merely replacing the child underneath that global guard still rejects bad
padding before any leaf query. The guarded acceptance theorem should compare
a source slot to the old slot conjoined with the appropriate per-slot padding
predicate, under the upstream size and batch/kind invariants. The raw old
helper alone is not equivalent.

The requested unconditional theorem is false, so no accepted-run multiset
transport, universal 1161 budget, `OraclePortHeadlineDVFrozen` endpoint, or
all-path ordered frozen caller join is asserted. Those items need the corrected
guarded theorem and source/caller invariants first. The compiled raw-helper
counterexample does not establish that such a corrected theorem is false.
No premise is deleted or retargeted, so no premise-deletion signature diff is
claimed. R19 and the existing draft endpoints remain byte-identical.
