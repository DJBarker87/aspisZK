# Accepted-log port — unmerged draft, 21 October 2026

Branch `codex/cx-acclog-draft-20261021`, based on the unmerged refinement
packet. Do not merge before user approval of the oracle port. Existing Lean
modules, S-cone re-pins, M10 instrumentation and production Rust are read-only.
All new proof modules have the `OraclePortAccLog` prefix.

## Stage 1: accepted schedules genuinely differ

`OraclePortAccLogSlot.accepted_slot_logs_differ` is an accepted **raw slot**
counterexample at height 18, batch 0, kind 1, with zero query indices, zero
oracle answers and a complete zero-filled slot. Both helper verifiers accept;
the frozen second read is another leaf (domain 0x11), while the recursive
model's second read is a parent (domain 0x12). Padding passes. Consequently
padding guard erasure cannot prove equality of the two accepted logs.
`levels_singleton` proves success symbolically by height induction; no concrete
height-18 recurrence normalization is used. This is not a witness that passes
the complete parser, semantic checks and full verifier.

`OraclePortAccLogPermutation.recovery_not_invariant` supplies a separate
counterexample for the actual `BinMerkleLeafRecovery.recover` primitive.
The exact complete height-three parent orders are:

```
recursive: A B C D E F G
level:     A B D E C F G
```

A/B are the left bottom parents, C their parent; D/E are the right bottom
parents, F their parent; G is the common root. C and D have distinct children
and the same digest 10. On the common root 13 and path [0,0,0], recursive
recovery returns the leftmost recorded leaf, while level-order recovery is
`none`: first-match lookup chooses D instead of C. These are equal node-table
multisets, and the permutation moves no entry across a commitment boundary.
This is a recovery-table counterexample, not a full frozen accepted protocol
run, and makes no claim against soundness outside the collision event.
Unconditional permutation invariance is false; collision-free invariance
would be a different theorem and would not supply literal log equality.

For the target's literal accepted-log equality, the model must adopt the
frozen order: stable ascending (index, source-position) leaf hashing including
all duplicates, immediate duplicate-digest checks, then padding validation,
then levels 0 through 17 with ascending live parent indices, consuming sibling
bytes consecutively, then the root/exhaustion check. Keep the outer six-slot
short-circuit order. Neither recursive postorder nor deferred duplicate checks
is that order. Existing modules remain unchanged by this packet.

## Stage 2: composition

Pending focused composition checks.

## Stage 3: accepted-run interface and headline

Pending focused interface and transport checks. The two-pass annotation
compiler must be covered explicitly; a one-pass accepted-only implication
does not identify the first pass when only the enriched second pass accepts.

## Evidence

Receipts: `evidence/acclog-draft-20261021/manifest.json`. Every attempt preserves
source, exact command, direct-import hashes and fingerprint, source revision,
exit, wall time, peak RSS, swaps, errors and full axiom reports. Failed
elaborations are retained and do not count as accepted proofs. Focused local
compilation uses the prescribed toolchain, -j1, -M4400 and shared mkdir lock;
objects are written only to this worker's private directory. No push or merge.
