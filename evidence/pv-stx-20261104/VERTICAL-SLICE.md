# D594 continuation: vertical slice INCOMPLETE

This is a source-local checkpoint, not a certificate of the requested
reject → redraw → success run. No privacy row or endpoint premise removed;
T and the original invocation domain are unchanged. No `source_entry_world`
was defined and no oraclePrefix/countTrace projection was fabricated.

## What is now checked

- `PV_STX_World`: source port of evh's event world and runtime state. File
  delivery/sync updates retain heap, allocator, entropy and handle frames.
- `PV_STX_EntropyWorld`: concrete interpretation of the existing entropy
  request family. Zeroizing constructors/borrows are transparent source-value
  operations; fill consumes the current entropy cursor. Partial Err buffers,
  source fail/div, faults and pending are represented. This handler does NOT
  interpret the new cleanup request family, and is not an entry certificate.
- `PV_STX_EntropyCleanup`: Rust lexical cleanup reconstruction in Code. On
  OS Err it converts the residual, restores the actual returned partial buffer,
  then requests the 64-byte drop. On rejection it increments retry, requests
  leaf, field, then temporary drops; success drops only the temporary. These
  are reached requests, not an externally supplied cleanup trace.
  `body_erases`, `PV_STX_CleanupBridge.loop_erases/generate_erases`, and
  `PV_STX_CleanupAccount.callMut_erases/next_erases` give full extracted-Result
  equalities under VALUE ERASURE. They do not prove native drop silence.
- `PV_STX_EntropyEndings`: actual exhausted source body/loop suffix, retaining
  the same world and no primitive calls. The loop return takes three machine
  transitions. This does not certify the sixteen preceding rejected draws.
- `PV_STX_NonceWorld`: port of create/open/write/sync operations; partial
  delivered bytes survive every answer, and failed sync does not commit them.
  `PV_STX_NonceSync`: actual `sync_directory` source lift, unconditional fixed
  erasure, and local open→sync machine substitution at the open post-world.
- `PV_STX_AllocatorWorld`: port from the evhB branch's generic allocator world.
  `denied_prefix` reaches an abort continuation after updating allocator/errno,
  preserving the allocation-event prefix and heap. `allocated_frame` proves
  file, entropy and handle frames. The actual V183 RawVec reserve and owner
  registry were INSPECTED ONLY; they were neither ported nor installed.
- `PV_STX_CallbackEffects`: port of evhB's argument-before-capture destruction
  as primitive Code requests, with complete local returned/fault substitution.
- `PV_STX_Diagnostics`: literal diagnostic bytes and reached destruction of
  an ignored writer error. It supplies neither an infallible writer nor the
  actual stderr syscall/guard implementation.
- `PV_STX_LoggedEntropy`: local full-answer records including exact request
  buffer, pre/post-world, partial writes and events. `two_draw_substitution`
  follows ruling (y) for two PRIMITIVES, not the source entropy retry loop.

## Primitive contracts and remaining associations

| Reached primitive | Request and world answer | Mutation/frame | Events/outcome | Actual slice installation |
|---|---|---|---|---|
| Zeroizing new/deref/borrow/restore | Original typed value, dictionary and backward continuation | Pure value restoration; world framed | No modeled primitive events; complete Result for AsMut | Existing entropy family only; source wrapper provenance retained |
| Entropy fill | Actual mutable Slice; `Provider w buffer : Answer Filled` | Non-pending answer advances cursor; files/heap/allocator/handles/resources framed | Request then delivery for returning answers; request for div/fault; partial Err Slice retained | Source cleanup/drop family still needs handler |
| Pending entropy | Same reached buffer and continuation | No committed draw/cursor advance | No events in this polling model | Native blocking/request-start event association OPEN |
| Source owner drop | Original owner value and lexical size (32/64) | Required: source byte writes/barriers, owner retirement and frame | Required on rejection/Err and temporary on success; abort skips unwinding | Request syntax + erasure checked; concrete source-local owner/drop interpreter OPEN |
| Nonce write_all | File, full requested Slice; typed answer plus newly delivered bytes/error bytes | Appends delivered bytes to matching file on every outcome; runtime frame retained | Request/write/optional error; complete source/fault/pending answer retained | Actual write_all syscall loop, file handle/cursor and pending progress association OPEN |
| Nonce sync/open/create | Original file/options/path; typed answer and created mode | Sync commits on Ok only; create adds file; other fields framed | Request/create/sync/error bytes | Source sync_directory lifted; reserve_fallible/path and cleanup continuations OPEN |
| Allocator | Layout/owner at current world; deny or address/backing plus post-backend/errno | Allocator/errno/count advance on denial; block installed on success; files/entropy/handles framed | Ordered request and reply; denial then abort in Code | Generic allocator port only; actual V183/RawVec ownership remains OWNER construction |
| Constructor callback drops | Original error then capture as typed primitive requests | Each child's modifies/frame must be discharged locally | All returned Result/fault prefixes preserved; pending retains request in Machine | Generic substitution checked; actual callback child destructors not installed |
| Diagnostics | Exact literal bytes; writer Result and owned error | Partial writer state and error destruction must persist | Error drop is a reached continuation; no fmt Unit semantics used | Literal Code port only; writer/guard/resource association OPEN |

Provider answers are primitive world data, not promises of OS adequacy. None
of these local contracts is added to T or to the endpoint as a new premise.
File/error encoders and allocator event encoding are not proved faithful to
the deployed observation by their types. In particular polling a pending
write with its original buffer is NOT yet a certified native write_all loop.
No model run or helper reply is advertised as deployed non-emptiness.

## Provenance and trust

`reuse-source/manifest.json` pins every inspected source to evh fd4a644fd4 or
evhB 058c4c764c. All reuse is by SOURCE PORT, not cross-cohort object import.
It distinguishes the generic allocator port from the unported V183 owner
implementation. `entropy-cleanup-generation.json` pins the Rust excerpt and
source changes; `generate-cleanup.py --check` reproduces the reconstruction.
This is source-control reconstruction plus kernel value laws, not a completed
native structural gate. The old ae1-2/D188 association and V370 remain named.
Physical L3 pairing is separate and was not introduced as a projection premise.

No new Kani/native/extractor run. Kani budget is zero. Historical entropy
harnesses containing writable statics receive no new credit (k3). The logs in
this work are local records. There is no claimed Kani caller/child certificate,
std parity check or matched native control in this checkpoint.

## Next construction

1. Interpret the cleanup request family with source-local owner identities,
   zeroization writes/barriers, restoration and frame/resource admissions.
   Reuse evh's ZeroizeArray/DeployedZeroWorld sources where appropriate, while
   keeping physical address pairing as the separate L3 residual.
2. Prove symbolic execution of the actual nonzero/entropy loop (not concrete
   normalization): rejected reply, fresh cursor, accepted reply; arbitrary
   rejected prefixes through limit 16; first OS error with partial writes;
   resource fault/pending before and after each reached call.
3. Install the original account/map_err and durable nonce reservation source
   continuations at that SAME world. reservation_path is a 10,004-line emitted
   term dominated by repeated SHA dictionaries: name/reuse symbolic dictionary
   components; do not normalize it or hide the helper behind a reply premise.
   Lift the nonce write_all syscall loop and handle/cursor cleanup explicitly.
4. Bind any existing Kani-bridged child using ruling (y)'s local log, declared
   modifies/frame and actual PacketDomain; keep suspended static-based credits
   suspended. No new Kani run is authorized by this checkpoint.
5. Only once the requested source slice is complete, define its entropy
   source_entry_world and derive projections from that one run. Then extend
   to full prove_for_proof_accounts. Fresh audit allocation is needed for the
   new closure: 91797–91799 were already consumed before this continuation.
