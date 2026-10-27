# LPm verifier::checkpoint native P6 bridge

**CLOSED — opaque-leaf bridge on the existing S2 checkpoint domain under narrowed
D188. No headline premise removed.** S2 / the deployed 100-bit target remain not
established. This is the approved hybrid native/Kani/Lean route, not a new
source-to-ELF proof or an assertion that Lean elaborates Rust.

The domain is EXACTLY the existing CheckpointBytes5Join.S1S7S8StateProvenance:
native variant S2, 64 actual accumulator weights, next=10, 22 queries below
262144, canonical saved fields and agreement with the reached model state.
Inputs/proof/public bytes are unchanged; in the physical use they are57607/1880
bytes. Each digest returns an arbitrary32-byte reply; SHA is never unwound.

For every input on that domain, porting native scalar words/bytes by their
natural values gives the cohort writer Result and the SAME chronological
attempted proof→physical-public→labelled-body digest sequence. The body used by
the third call is the one produced by header/state/root/field/query/alpha/Z/
claim/rhs/power writes and all64 actual weights, and the returned bytes are
that SAME body followed by that call's reply. Result length1768, body1736.

The exported carrier theorem is `AspisR1.LPm_CheckpointLeaf.native_result`.
Its LOCAL trace contains linked prefix appends, the actual weights' per-step
trace and the final checksum append. It has no whole-body/result equality,
independently selected field inventory or whole accepted-run hypothesis.
Universal native gates, the exact source partition and the list/field inductions
below construct that trace for the frozen function, as in the LPk hybrid pattern.
`LPm_CheckpointProgram.program_eq` separately identifies the complete reified
program, so equality is not merely equality of successful output bytes.

## Pins and source association

Frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
crates/aspis-r1-cost-probe/src/verifier.rs:326, SHA256
8c872d42bdaa245cc540be6b26d17108a5cb40754b8befb79e147f5843b1f756.
LPm_ASSOCIATION.json pins the complete checkpoint body's exact text and all13
ordered source partitions. The only source effects between the first two reads
and checksum are these append-only writes to the one local Vec; p/a/proof/public
are shared inputs and never replaced. Both rho/power and every E/Q field use the
same operands inventoried by the cohort's `CheckpointBytesBody.fields p a`.

The coherent SInt2 workspace and its objects are reused read-only. Only two
missing unchanged LPi prerequisites were rebuilt privately, in L001/L002.
LPe→LPf→LPi's retained scratch is reused, including LPi's documented frozen reset
of obsolete field-contract instrumentation; it is not a second corpus. Earlier
patches and qualified frozen replays are pinned in LPm_ASSOCIATION.json /
LPi_REUSE.md. Only an LPm cfg(kani) registration and new LPm harness module are
added to that scratch. All498 frozen files, locally AND remotely, match after
removing exactly the listed scratch registrations (LPm_SOURCE_AUDIT.json).

Every Kani run has a fresh exact frozen package/edge graph validation, offline
execution, and frozen lock hash5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef
before AND after. Tool pins: LPm_tools.sha256. Harnesses are patches/receipts only.

## Checked composition

| Stage | Accepted evidence | Exact association |
|---|---|---|
| Header | Inherited LPe_K015 | Actual S2 tag/next cast/magic/flags; existing provenance supplies S2 and next10. |
| First two reads / state | LPe_K016, LPi_K018; new K004 | Same input slices/replies, chronological order and state bytes; arbitrary-prefix32-byte append/frame. K018 covers actual57607/1880 carriers. |
| Roots / queries | LPe_K017; K004/K005; existing CheckpointBytesQuery/F3K_WordCodec | Exact immutable roots/query order; every query's native LE word byte and arbitrary-prefix frame, all U32s. |
| E/Q serializers / put/put_k | LPi_K012/K013, LPi_WriterValues; L007 LPm_BytePorts.e_source | Arbitrary-prefix0..1720/0..1704 native private callers. Total emitted serializers with exact byte values; explicit eight-word E owner port. No new unpaired stub. |
| Alpha / Z | LPe_K019; LPi fold; L018 LPm_FieldCarriers.semantic_values/coordinate_values | SAME actual10 semantic values and nested2-point x/y order, transported to10/4 source field lists, with append-only arbitrary-prefix induction. The inline16-byte writer body is the same body as put_k. |
|64 weights | K001, K003; L004 LPm_WeightLoop.* | Actual Vec suffix/head/tail/exhaustion; shared-reference dereference and native put_k; ONE arbitrary iteration, then induction on the actual accumulator carrier. No whole-buffer loop verification. |
| Domains | L016 LPm_CheckpointDomains.* | SAME prefix trace yields712 bytes; every reached712+16*i prefix lies in the proved writer domain; semantic/Z/query/E domains fit without strengthening. |
| SAME body / third call / return | LPi_K018; L006/L013/L019 | Concrete field inventory, linked prefix+weight states, third digest of that derived body and last append; full cohort Result AND ordered log from local calls. |
| Model program | L009 LPm_CheckpointProgram.* | Equality of reified read programs for all replies; no output-only promotion. |
| Consistency | L017 LPm_CheckpointWitness.all_replies | Linked local trace exists for every domain input and arbitrary three replies; not a claim of joint headline-premise inhabitation. |

Native scalar ports are injective on complete QM31 carriers
(LPm_FieldCarriers.q_values_injective). `indexed_values` / `weights_port` identify
whole arrays with their actual indexed traversal, rather than another array of
matching length. The original E serializer's P6 iterator interpretation remains
explicit; the new type port reuses its existing output theorem. No multiplication
is re-proved in Kani. LPm_STUBS.md names every installed replacement/domain.

## Failed shapes and validation

K002 combined full weight Vec and arbitrary-prefix writer timed out at90s.
It is excluded and never rerun. K001 traversal plus K003 selected-reference
continuation split exactly at the borrow, keeping the SAME selected word and
remaining iterator; LPm_WeightLoop composes their local transitions. No timeout
or cap increase. Own solver TMPDIR was empty after the timeout.

Rejected Lean snapshots are retained in full: reserved binder names, missing
namespace import, list-map rewrite elaboration, section-variable/doc placement,
and a reducibility attempt that reached the default recursion limit. SourceBody
is now kept opaque and rewritten symbolically; no option limit was raised.
Failed error-recovery sorryAx prints are excluded, never accepted as an audit.

Through L019:19 Lean compiles (11 pass,8 rejected proof errors),5 Kani runs
(4 pass,1 timeout). Two of the Lean passes rebuild unchanged missing dependencies.
Each attempt records exact target/command, source revision/hash, deps/tool pins,
exit, wall, peakRSS, swap and full axioms lines. L019: exit0, wall2.117157151s,
RSS4344592KiB, swap0; native_result uses only propext/Classical.choice/Quot.sound.
All accepted new tops use a subset of those standard axioms. K001:673 checks/
3 covers; K003:398/3; K004:379/3; K005:375/3, all pass (unreachable checks retained).
All scopes serial/admitted exit0 AND allowed:true,6G/8G/swap0/tasks64; Lean-M7000;
Rust optimized. No shared launcher, monitor, admission script or object changed.

## Retained boundaries

No headline import, theorem binder, carrier, adversary, failure event, numeric
bound, trust item or shipped source changed. Headline remains
AspisR1.RPx_Deployed.deployed; L154 remains its statement parameter. This closes
one native P6 leaf on the existing domain; it does not prove its enclosing S2
caller/runtime/heap/ABI/source-to-ELF admissions or joint headline non-vacuity.
Allocator, pinned Rust/library/compiler and adopted runtime/library trust remain
as recorded; no extra cryptographic assumption is introduced.

Repository crates/programs stay frozen; ELF rebuild trigger did not fire.
Inherited pins, NOT newly reproduced:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

All commits local; no push, merge, other-worker worktree/candidate edit or key
operation. Next leaf is prepared_claim, still OPEN.
