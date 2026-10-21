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
