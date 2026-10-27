# LPn r1_semantic::claims — CLOSED

CLOSED as an opaque-leaf P6 bridge for every genuine adopted Prefix, its SAME
3717-byte framed row25, arbitrary payload bytes, all three29-value decodes,
first-error prefixes, three owned writes, initialization and cleanup. No
headline premise removed. Allocation outcome is explicit; no malloc-success
precondition is imposed on the caller.

## Exact statement, allocation and reference

Native Result is represented by `LPn.Claims.owned reserved p`: on the actual
allocation failure it is Error::Allocation, with no decode/store suffix; on
allocation success it is the existing cohort's `r1_semantic.claims p`, with the
SAME returned three rows or decoder error. `native_result`, `native_success`,
`native_error`, `allocation_rejection` and `accepted_to_cohort` export this
association. The last theorem DERIVES reserved=true from successful owned
return, then transports the SAME output to the cohort. It does not assume
malloc success, invent an accepted execution, or weaken a headline binder.

The raw cohort model has no allocation-failure arm. Consequently no
unconditional equality of the raw cohort Result and native Result including
OOM is claimed. The explicit owned reference preserves that failure partition;
accepted-run refinement suffices at this opaque leaf because native Allocation
rejects before any decoder/query/effect suffix. This is the existing Allocator
returning-behaviour boundary (C3-BIN native Vec/Box ruling,c), not a new trust
item or a claim that unsafe code is covered by D188. All unsafe writes and
assume_init are checked natively below. The existing owned predecoded-row
reference, cohort model and its three-stage laws are reused; no fresh Charon
or package-wide replay is claimed.

Frozen source4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
r1_semantic.rs:42–55 and aspis-core/r0/heap.rs::uninit. Source order is token25,
fallible heap allocation, decode29 offsets0/29/58 and corresponding raw writes
in point order, then assume_init. Error leaves the owned MaybeUninit box in
scope for actual Drop; plain QM31 rows have no destructor. There are no digest,
oracle, syscall or external input mutation operations in this leaf.

## Native and formal association

| Stage | Evidence | Exact scope |
|---|---|---|
| SAME token | inherited new K008 + L066 read25/record | Actual Prefix getter supplies exact row25/stored slice; model index25 derived from27-entry carrier, no read premise in native_result. Upstream parser framing remains its caller cone. |
| Complete decoder | LPn_decode_k_LEAF.md | Full N29 arrays and all errors on SAME record; neither sparse examples nor independent successful rows. |
| Native owned write/init | K011 | Real heap::uninit; arbitrary point0/1/2, two arbitrary prior rows and arbitrary returned29-cell row; arbitrary initialized-prefix observation/lane. One verbatim raw write preserves earlier initialized rows, SAME owner pointer; at final point every row/lane is readable and assume_init returns the SAME owned pointer/values. No future uninitialized slot is read. Actual Drop executes in both partial/full cases.449 checks,0 failed,5 unreachable. |
| Native error cleanup | K012 | Real allocation, arbitrary initialized prefix, failing child `?`, exact error row/index, no later write/assume_init, actual MaybeUninit Drop. Allocator error retained.378 checks,0 failed,5 unreachable. |
| Model call/storage induction | L065 | Step has only child rejection/row append/no-call stopped cases on SAME record; stages_eq induction, exact successful prefix length, full fromRecord/finish join. Stopped states are inactive padding after source rejection, not extra native calls. |
| Prefix and Result | L066 | Exact fixed index25 read derived; full state/owned Result, returned Array carrier, allocation reject and accepted-to-cohort transport. |
| Complete source domain/totality | L067 | Every bounded Ready decoder has some exact Result; every point's guard/domain derived from3717-byte row and point<3; all three-stage traces exist including errors. No supplied canonicality, success result or array equality. |

K011's arbitrary bit patterns represent only nested u32 products; no pointer,
reference or enum is fabricated. Field-value mapping is the CLOSED decode
bridge's coordinatewise natural-value map, not an assumed raw layout. No
canonicality restriction is necessary for storage. K011's prefix invariant
requires only earlier initialized rows, exactly what previous writes supply;
K012 handles exit before the next initialization. At point2 the pointer/range
checks and arbitrary row/lane observation cover all87 cells, so all fields of
the returned object are initialized before assume_init. Native frame checks
are ONE iteration; Lean performs the three-step induction, never a whole-buffer
native verification.

The safe logical reference stores a list of completed typed rows and appends
one exact decoded row. K011 proves its reached native storage association and
final ownership; K012 proves rejection/cleanup; L065 identifies that safe state
with the unchanged owned-reference/cohort three-stage laws. No native output,
whole-body equality, callback law or independently chosen accepted run enters
as a hypothesis. Prefix observations and every decode use ONE stored slice.

## Non-vacuity, evidence and retained boundaries

L067 constructs local traces for every genuine row, including malformed low
limbs; Scan/Decode trace totality is reused, not a success hypothesis. Native
zero decoder non-vacuity K010 plus the arbitrary returned-row storage K011
supply the local zero success construction; the three-step total/length laws
compose it. No joint inhabitant of all headline premises is claimed.

No stubs or multiplication. L061–L064 are exact import/name copies of old
DotModel/monadic/Claims laws required by the inherited reference; their body
hashes are in LPn_TRANSFORM.json. L065–L067 all pass, printed standard logical
axioms only. K011 wall30.333923637s/RSS1,108,904KiB, K012 wall3.522892377s/
RSS398,292KiB, both swap0. Full receipt/source/tool/command/revision/dependency
pins and axiom/N/A lines retained. Fresh exit0+allowed:true admissions,6G/8G/
swap0/tasks64, one scope at a time; Lean-M7000, optimized/offline frozen graph
and unchanged lock per native run. No timeout/cap increase or failed-shape rerun.

Compiler/platform/library/P6 association, standard axioms, existing allocator
returning behaviour and upstream Prefix parsing remain named boundaries.
No concrete headline/caller installation or source-to-ELF proof is supplied.
AspisR1.RPx_Deployed.deployed, frozen3, RuntimePersistence, L154 statement
parameter, game/metric/failure event and narrowed D188 unchanged. Target not
established. Shipped files unchanged; ELF pins inherited, no rebuild trigger.
No push, merge, session A/candidate or key cleanup operation.
