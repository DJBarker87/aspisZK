# Exact missing native/source facts

The requested `PoolU_Write.accepted_p1_writes_copy` is NOT established. The
native acceptance antecedent cannot be connected to `PoolU_CopyTail.accepted`'s
reference prelude. This is a source-refinement gap, not a cryptographic assumption
or a reason to enlarge SDK/runtime trust. No accepted attacker-chosen native
write was found. Do not claim any global ledger removal.

## Earliest enclosing source gap

Need a source-indexed native/P6 decomposition of
`plan_pair_forest_checkpoint_accounts_v1` F744–789 on the ORIGINAL production
`AccountInfo` records, master/lane structs, output struct and heap. Inputs are
fixed before execution: program id, actual master key, the exact eight lane
handles, actual checkpoint key, full account cells, live SDK tokens, allocator
and oracle/syscall state. For every result, derive the SAME sequence of reached
calls and outputs, including mapped errors and earlier effects:

1. Exact lane count, alias check; master Box allocation and F430–457 decode:
   program-account metadata, nonsigner, shared borrow, strict master decoder,
   stored-bump address check and decoded identity.pool = actual master key.
2. Eight ordered F507–544 lane decodes from those same handles: metadata,
   stored-bump borrow, fast PDA path OR fallback search, signer/key rejection,
   strict tree decoder, master/id/bump equality; Vec allocation/push, boxing and
   fixed-array conversion, with actual cleanup on every early exit.
3. Actual `each_ref().map` root array and global-root call; actual checkpoint
   PDA `[checkpoint seed, actual master key, decoded next sequence LE, bump]`;
   original pure planner invocation; first fresh-PDA call; both encoders;
   exact `PlannedPairForestCheckpointAccountsV1` fields returned, without
   substituting a separately successful invocation or separate snapshots.

Existing Hiq metadata facts certify their guards only. There is no retained
successful Kani/native-to-P6 certificate for the three joins above in the
PoolW/PoolV/Hir inventory. A hand-written Lean slice with unconstrained decoder,
PDA and allocation operations would leave precisely their native interpretation
unproved; treating that as an instantiated native join would add a new premise.
The prior full caller extraction failed at AccountInfo slice indexing and did
not produce that reference body. No failing extraction was rerun.

## Original unrestricted planner decomposition gap

`PoolV_K023` proves the projected chronology tail, K024 the projected lane loop,
and K025 assembly/validation on original production output/master types.
They do not prove that the ORIGINAL pure planner at pure488–548 reaches those
slices with the same projected values and error/effect state after its initial
master/mask/global-root checks. Need this actual structural decomposition,
including `lanes.iter().enumerate()` bindings, roots/global combiner and original
struct projections; alternatively, a complete checked accepted-result law of
the original unrestricted planner. No restriction on roots/frontiers/policy or
other decoded fields may be imported from PoolW's narrower coherent class.

Original full planner output/chronology gates W018/W019 timed out. V002 scalar,
V014 selected-output, V016 progress, V018 overflow, V019 sequence, V020 duplicate
and V021 sequence-binding checks did not pass. Successful V015 monotonicity,
V017 mask and V022 capacity do not imply output binding/progress/increment.
The successful projected checks are retained; no failed gate is promoted.

## Caller, System-CPI and canonical-action join

Given that actual returned plan, need native/P6 decomposition of F2130–2188:
AS8C decoder, exact12 count, unique actual keys, role indexing, payer/System
checks, actual planner call, SECOND fresh preparation, optional decode of the
SAME planned192 image into sequence/bump/signing seeds, original System helper,
post-CPI guard, master borrow then checkpoint borrow, complete copies and
compiler cleanup. Preserve each earlier error and effect and omit unreached
suffixes. Output bytes must be tied to that invocation's physical keys and
canonical committed action, not an arbitrary id attached after the proof.

W012 native copy and V011–013 arbitrary-image borrow errors are local tail
facts. V009–010 supply native guard/P6 coupling; no new zero-loop proof is
needed. V003–008 cover six recorder error positions; W037/038/040 cover recorder
success order/arguments. These do not establish caller seed construction,
Rent::get, allocator/Vec/Box cleanup, arbitrary actual runtime effects or the
caller-to-runtime association. Actual System and Solana ownership/CPI/syscall
semantics remain under the EXISTING external runtime interpretation. Route-B
SDK trust does not include CPI. No new runtime item is requested/adopted.

The new CopyTail theorem starts from the post-prefix store, so it permits
System CPI to change balances/owner/size before copying. Its metadata frame is
ONLY from that store to post-copy. Reusing it as a pre-transaction lamport or
owner frame would be invalid. It assumes distinct actual master/checkpoint keys;
that premise must be derived from the native unique-account guard, not supplied
for independently selected buffers. Its prelude is an EXPLICIT parameter and
is not an implementation instance.

## Downstream interface

Phase2 needs native successful P1 -> exact192 encoded ASC8 at actual key, marker65,
actual master update, metadata/other-account post-CPI copy frames, source
error/effect prefix, and same-action association; combine with occupied-target
rejection and other live-handler/close/CPI noninterference. The current reference
tail alone supplies none of the native acceptance antecedent.

Runtime history needs this local write event associated with its actual source
invocation/key/store and canonical transaction commit; actual genesis/zero-owner
assignment, alias coherence, failed-child/transaction rollback and retained
load/reader association remain separate. Existing Hist/Hiq/Hir native CP child
and copy observations must be kept: CP1768 is distinct from ASC8192. P1 does not
write a verifier post-CPI copy. Upstream master/lane correctness and same-world
proof/public query/binding experiments remain separate.
