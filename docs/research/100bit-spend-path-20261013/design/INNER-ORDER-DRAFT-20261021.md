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

## Stage 4: handoff and reproducible audit

Inspected source mapping (all under `crates/aspis-r1-cost-probe/src/`):

| Frozen source | New definition |
| --- | --- |
| `candidate.rs:92–113` sorted index/position keys | `sortedPositions` |
| `candidate.rs:173–195` sorted leaf loop and duplicate exit | `hashLeaves` |
| `multiproof.rs:54–59,85–110` well-formed/count | `wellFormed`, `countLevel`, `nodeCount` |
| `candidate.rs:196–202` count/capacity/zero padding | `slotTail` |
| `multiproof.rs:147–169,187–193` binary live-prefix loop and final comparison | `runLevel`, `runLevels`, `verifyInPlace` |

The list representation, Nat arithmetic, and logical conjunction in the pure
final check require a future refinement theorem under the source live-prefix
invariants. The intended equivalence of pair tests uses strictly increasing
indices. No proof of source checked-integer totality, stable-sort refinement,
or full parser/caller reachability is included. The definition covers the
binary branch only; it does not purport to model the eight-way branch.

All four new modules compile. There are 19 new theorems and 23 accepted
axiom reports, all subsets of {propext, Classical.choice, Quot.sound}.
The five receipts include four successes and the corrected elaboration
failure. Peak RSS is 3,650,830,336 bytes; every attempt reports zero swaps.
Final focused import `OraclePortInnerOrderFreeze`, attempt 1: exit 0,
10.607074750121683 seconds, peak RSS 3,558,785,024 bytes, zero swaps.
Each receipt includes exact command/target, source revision and SHA-256,
direct-import hashes, dependency/environment fingerprint, exit, wall time,
RSS, swaps, complete axiom lines and errors. The local cap is -M4400,
with the prescribed shared mkdir lock and private object directory.

This reuses historical cached imports read-only and is **not** a coherent
frozen manifest replay. No full regression, Rust suite or build-host job was
launched. The false helper statement is the obstruction; larger resource
limits would not repair it.

Run the read-only audit with:

```sh
python3 -B tools/oracle-port-inner-order/audit.py
```

`frozen-sources.json` pins the final new Lean sources and unchanged inspected
source/model/headline files. The audit checks additive scope, final source and
receipt hashes, standard axioms and every new theorem's audit report. No
existing Lean module, S1/S3/S4/S5/S9/S10 candidate or M10 instrumentation file
was changed. No wallet/key operation, push, merge or deployment occurred.
The lead must retain this as an unmerged draft pending user approval of the
port. The proposed corrected theorem and the endpoint remain open.
