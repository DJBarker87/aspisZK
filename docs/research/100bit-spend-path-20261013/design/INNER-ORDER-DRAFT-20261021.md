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

Pending focused counterexample compilation. Existing `verifySlot` does not
check padding or slot width. The requested unconditional equivalence must be
tested against that actual signature before it can be used for a headline.
