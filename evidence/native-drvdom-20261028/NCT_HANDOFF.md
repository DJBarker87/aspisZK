# Driver-domain audit (stage 1)

Target not yet established. This lane is Lean only; no native gates run.

Before: `KNE_Caller.DriverEstablishedDomain Reached := ∀ p a,
Reached p a → ∃ pm am, S1S7S8StateProvenance p a pm am`.
`Reached` is an arbitrary predicate supplied by the enclosing caller, not a
native reachability definition. Its p/a carriers are the checkpoint writer's
Prepared/Accumulator. Existential pm/am are their exact numeric field
interpretations, not independently fixed transcript/model states.

Provenance contains S2, 64 weights, all 22 queries <262144, CanonicalFields
(gamma/kappa/alpha/rho/semanticAlpha/coordinates/claim/rhs/power/weights), next10,
and equality to the SAME interpreted pm/am. It does not itself assert final_len;
KNE_Schedule.caller_final_len derives 64 from S2 transport arithmetic.

NCL_DriverCuts.accepted covers one emitted CurrentCaller candidate.tx1 with
observer none, successful `ok (.Ok saved)`, and OFF_FOLDED_ROOT=7751,
OFF_ROUND1=7783. It derives split10 and cuts of that same call. The dictionary,
digest, semantic/public/proof/hash and saved Vec stay indexed together.
NCL_DriverForward.source replays precisely those cuts at split10; it adds no
state canonicality guarantee. On arbitrary Ops, the child operations are
abstract. Installed Configuration still contains abstract preparation and
query primitives. Neither theorem's conclusion is a provenance record.

The strongest available control theorem Tx1Q_Control.fields derives weights64,
next10 and canonical flushed weights from installed query/pending/flush calls.
This is smaller than CanonicalFields for every writer field. Accepted-run cuts
also do not establish reachability for calls in runs that later reject/fail/diverge.
No all-native-reached-calls claim is made.

Plan: check the co-import and exact printed statements; derive installed model
control from NCL cuts without reproving child facts; explicitly retain any
unproved S2/query-bound/full-canonicality gates in the strongest composition.
Native/model call identification remains the open owner transport decision in
`docs/research/100bit-spend-path-20261013/design/COMPOSITION-TRUST-DECISION-20261028.md`
or the driver's own native bridge. This packet cannot adopt that decision.

Stage-1 validation: NCT_L001 compiled NCT_Audit.lean with the actual co-imports;
exit0, 2.221831s, peak RSS5347848KiB, swaps0, revision4e647af907.
The printed roots use only propext/Classical.choice/Quot.sound. Full statements
and receipt are NCT_L001/stdout.log and NCT_L001/receipt.json. Both seed caches
were COPIED to the own retained cache; per-file source hashes are NCT_CACHE_COPY.json.
No shared cache was written. This focused audit is not a release replay.

## Stage 2: strongest checked domain assembly

`lean/NCT_DriverDomain.lean` defines `Reached c p a` as the existence of one
NCL cut on `currentInstalled c/currentDigest c`, with p/a exactly the carrier
maps of cut.prepared and the SAME cut.out after replacing weights by cut.flushed.
It is not a new model implementation or a declaration of native reachability.
`of_accepted` constructs it using NCL_DriverCuts.accepted. `replay` uses
NCL_DriverForward.source with the SAME semantic/pub/proof/saved, under the same
two offset equations. The predicate itself contains cuts; offset equations
are required for their replay, rather than silently asserted by its definition.

`control` assembles the existing Tx1Q_Execution.Run from those exact cut
carriers using the existing initial/pending/geometry/query/flush transports.
Tx1Q_Control.fields supplies next10, weights64 and canonical flushed weights.
`reached_weights` transfers those coordinate inequalities to the writer's raw
weight fields. No arithmetic recurrence or child control fact is reproved.

After (conditional):
`established c variant queries canonical : DriverEstablishedDomain (Reached c)`.
The three RETAINED, unproved gates quantify over the SAME Reached c:
1. p.variant=S2;
2. each of the 22 p.queries is <262144;
3. `NonWeightCanonical (fields p a derived_size derived_queries)`:
   gamma, kappa, both alpha, rho, ten semanticAlpha, four coordinates, claim,
   rhs and power are canonical.
The record is explicitly organisation, not discharge. We do not claim the
remaining gates are impossible to derive with further preparation/arithmetic
proofs; they are not conclusions of the audited NCL cut/replay interfaces.

Discharged: weight length, next and all 64 weight canonicality obligations.
Retained: S2/query bounds/non-weight canonicality. pm/am are the SAME exact
`CheckpointBytesBlocks.prepared/accumulator` built from those raw fields, with
both provenance equalities rfl. This does not identify pm/am with a selected
transcript's semantic execution; KNE's existential contract does not ask that.

NCT_L002 failed on an existential binder syntax error; error-recovery sorryAx
outputs receive ZERO credit. Rejected source is retained. NCT_L003 passed the
initial assembly; NCT_L004 passed the strengthened weight-canonicality assembly,
exit0, 2.393719s, peak RSS5381180KiB, swaps0, revisiond97db4e276 plus source
hash in receipt. Every six new theorem roots has standard axioms only.

## Stage 3: same-call conditional leaf composition

`NCT_DriverDomain.native_result` now takes an explicit NCL cut and the three
pointwise field gates above. There is NO DriverEstablishedDomain or WriterDomain
argument. `callDomain` constructs the writer domain using the proved control
and weight facts, and `KNE_Leaf.native_result` supplies the complete leaf result.
This is a partial premise discharge: the field gates remain premises, not a
new unconditional model-driver closure.

The exact semantic/public/proof/saved of that cut are retained. The writer
Prepared is `toPrepared (Tx1Q_Carriers.prepared cut.prepared)`; the Accumulator
is `toAccumulator (Tx1Q_Carriers.accumulator {cut.out with weights:=cut.flushed})`.
The digest is the existing `VTop_Checkpoint.digest (Tx1Q_Install.digest
(currentDigest c))`, with Unit hash (). No independent digest, second proof,
public input, accumulator, accepted execution, saved checkpoint or output
equality is added. Port3_CheckpointInstall.writer_run on cut.checkpoint and
same-run determinism derive `out.val = saved.val`.

After: for this cut, under explicit S2/query/non-weight-canonicality gates plus
the unchanged leaf's local append correctness, same-body trace/checksum write,
oracle interpretation and three digest calls:
- sourceFinalLen=64;
- output bytes are the cut's saved Vec bytes and length1768;
- output is LPm_CheckpointProgram.returned for these exact fields;
- writer run has the SAME chronological proof/public/checksum read log;
- bytes equal OraclePortCheckpointAbiC5.encode for the SAME pm/am.
The `native` relation here remains the leaf's abstract local append relation,
not an assertion that a native enclosing driver has reached these arguments.

NCT_L005–L007 are rejected drafts (notation namespaces, proof section binders,
and captured notation free variables respectively). Their source snapshots and
full errors are retained, all recovery sorryAx outputs uncredited. NCT_L008
checks the final same-call composition: exit0, wall2.472852s,
peakRSS5384916KiB, swaps0, revision8a098e8591 plus exact source hash in receipt.
All ten NCT roots use only propext/Classical.choice/Quot.sound.
