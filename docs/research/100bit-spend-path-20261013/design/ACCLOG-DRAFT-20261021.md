# Accepted-log port — unmerged draft, 21 October 2026

Branch `codex/cx-acclog-draft-20261021`, based on the unmerged refinement
packet. Do not merge before user approval of the oracle port. Existing Lean
modules, S-cone re-pins, M10 instrumentation and production Rust are read-only.
All new proof modules have the `OraclePortAccLog` prefix.

## Stage 1: accepted schedules genuinely differ

`OraclePortAccLogSlot.accepted_slot_logs_differ` is an accepted **raw slot**
counterexample at height 18, batch 0, kind 1, with zero query indices, zero
oracle answers and a complete zero-filled slot. Both helper verifiers accept;
the frozen second read is another leaf (domain 0x10), while the recursive
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

The follow-up modules strengthen that example without changing the endpoint:

- `OraclePortAccLogRecoveryLog.byte_log_recovery_not_invariant` uses actual
  encoded byte logs and `RawCutRecordedWordsExecutableBin.recoverAtExec`,
  with the existing parsers. It is not just an abstract table lookup.
- `OraclePortAccLogRecoveryWorld.consistent_byte_log_counterexample` proves
  both logs are consistent with one explicitly constructed total oracle.
  The shared digest is an intentional collision, never inconsistent answers
  at one address.
- `OraclePortAccLogParentSchedules.source_parent_schedule` and
  `recursive_parent_schedule` evaluate the actual generic `runLevels` and
  recursive `OracleDecisionMultiTree.execute`, at height three with prehashed
  leaves. They produce exactly the displayed seven-parent orders and the same
  root 13. Thus this is the specific level-versus-recursive permutation.
- `OraclePortAccLogCuts.same_frame_recovery_obstruction` puts the same frame
  after either block and proves the actual first-frame cuts recover exactly
  the respective logs; recovery still differs. Its empty frame isolates the
  cut primitive and is not claimed to be a complete protocol transcript.

These focused witnesses do not establish a full frozen accepting protocol
counterexample or refute a collision-charged recovery transport theorem.
They establish why unconditional permutation invariance cannot repair literal
accepted-log equality to the existing recursive model.

For the target's literal accepted-log equality, the model must adopt the
frozen order: stable ascending (index, source-position) leaf hashing including
all duplicates, immediate duplicate-digest checks, then padding validation,
then levels 0 through 17 with ascending live parent indices, consuming sibling
bytes consecutively, then the root/exhaustion check. Keep the outer six-slot
short-circuit order. Neither recursive postorder nor deferred duplicate checks
is that order. Existing modules remain unchanged by this packet.

## Stage 2: composition

`OraclePortAccLogCones` proves exact evaluated-log/value equality composes
through `bind` and the complete continuation-sensitive `Calls` tree. Existing
`ConeJoin` implies `ConeLogJoin`; the latter retains every intermediate return
value and state as well as the ordered log, including ordinary errors.
`acceptedVerifierJoin_of_cones` lifts these obligations with the existing S10
inventory and explicit source/model caller identities. `short_accepted_eq`
proves accepted-only equality suffices for Boolean children of the outer AND.
`acceptedRunJoin_of_cones` additionally uses source verdict stability under
annotation enrichment to cover both passes.

These are conditional composition theorems. The general frozen-to-current-
recursive-slot accepted-log obligation is false on raw helper inputs by Stage
1; no actual frozen whole-decision join is constructed. Per-cone source pins,
caller inventory, checked arithmetic and upstream reachability remain owed.
Total S-cone statements needed by R22 are not weakened by these accepted-only
consumer facts.

## Stage 3: accepted-run interface and headline

`OraclePortAccLog.AcceptedRunJoin D rust` is verbatim:

```lean
structure AcceptedRunJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop where
  verifier : AcceptedVerifierJoin rust (verifier D OraclePortShortCircuit.outerDecision)
  annotated : ∀ (P : Prover) H,
    (eval H (annotatedWith D rust P)).2.2 = true →
      eval H (annotatedWith D rust P) =
        eval H (annotated D OraclePortShortCircuit.outerDecision P)
```

The first field uses this verbatim definition:

```lean
def AcceptedVerifierJoin (source model : Verifier) : Prop :=
  ∀ H i, (eval H (source i)).2 = true → eval H (source i) = eval H (model i)
```

Both fields retain **ordered** reads and answers and the entire returned
carrier. The annotated output includes public statement, stored bytes and
the enriched proof containing the recovered words. No rejection equality is
required. The second field is deliberately stronger than the first field
alone: it covers the two actual annotation passes. It is not claimed to
follow from one-pass acceptance inclusion. `acceptedRunJoin_of_stable` gives
a sufficient lifting rule from the raw join and source verdict stability
under proof enrichment; source owners may prove those facts instead of the
annotated equality directly. The headline has no additional stability
premise: it consumes the explicitly quoted two-field join.

`executionJoin_acceptedRunJoin` and `outerExecutionJoin_acceptedRunJoin`
prove both inherited joins imply this interface. `acceptedRunJoin_strict`
and `acceptedRunJoin_outer_strict` prove strict weakening against each old
interface at the actual fixed models, using a tag-zero rejecting input and
an extra query only after rejection. Their witnesses cover annotation too.
These results compare logical predicates; they do not construct the frozen
source join.

`OraclePortAccLogTransport` proves equality of first-pass built words on
accepted first passes, and equality of decoded public data, initial words,
final words and the actual extractor on accepted annotated runs. It then
proves the unchanged runtime failure-mass transfer using the retained
`StoredCarrierBinding` and the actual `failureMass`. Rejected runtime runs
have zero mass. There is no replacement acceptance-only bad-input event,
new extractor, multiset rewrite or monotonicity assumption.

The compiled endpoint is
`OraclePortHeadlineAccLog.final_soundness`, in the distinctly named new file
`OraclePortAccLogHeadline.lean`. It retains `OraclePortHeadlineDVsc.Claims`
verbatim: accepted model extractor cost, returned-witness relation, abort
allowance, total runtime bound and the same per-query range. The separate
`per_query` theorem also compiles. The exact signature diff against
`OraclePortHeadlineDVsc.final_soundness` changes **only**:

```diff
-    (h_Rust_equals_dV : OuterExecutionJoin D rust)
+    (h_Rust_equals_dV : AcceptedRunJoin D rust)
```

See `evidence/acclog-draft-20261021/headline-signature.diff` and the complete
before/after signatures. The replacement is quoted verbatim above and proved
strictly weaker. No premise deletion from the current R19 release endpoint
is claimed. R19, its free decision, boundary hypotheses and source/runtime
obligations are unchanged. This is a conditional draft port endpoint, not
an unconditional frozen-source soundness result. The cached closed M10
ledger is reused read-only; no concurrent instrumentation file is changed.

## Evidence

Receipts: `evidence/acclog-draft-20261021/manifest.json`. Every attempt preserves
source, exact command, direct-import hashes and fingerprint, source revision,
exit, wall time, peak RSS, swaps, errors and full axiom reports. Failed
elaborations are retained and do not count as accepted proofs. Focused local
compilation uses the prescribed toolchain, -j1, -M4400 and shared mkdir lock;
objects are written only to this worker's private directory. No push or merge.
