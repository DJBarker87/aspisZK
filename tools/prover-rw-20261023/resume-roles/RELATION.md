# Concrete roles, projection and remaining producer

This supersedes ONLY the missing-success-witness assessment in ResumeScalar.
Original packets remain unchanged. No theorem statement/premise changed:
before = after = the complete resume contract in resume-p6/SOURCE-CONTRACT.md.
There is no output-equivalence premise. All nonce32/postbuffer64, entry0..15
and Ok/all valid NonZeroI32 error cases remain. No assumptions discharged by a
new native theorem; no trust, freshness, independence or error law added.

## Recovered emitted success path (reused054)

association.json retains the full structured resume body, types, exact paths,
spans and selected operands. It is compiler-derived Charon LLBC from old054,
not fresh Rust MIR or accepted Aeneas semantics. Complete selected source is
identical under ProverRwFactoryState -> ProverRwResumeScalar rename. The hook
library differs; this does not identify the current scalar build.

Root601 matches outcome4. On Ok, field scan sets38; outer569 true evaluates
leaf scan into43; inner455 true is empty. Its false arm performs rejection
and Return454. Therefore the true arm continues at the ENCLOSING block suffix:

| Statement | Actual source place/operand |
| --- | --- |
| 465 | Copy request2.mask_nonce (field0) to52 |
| 467 | Move field_mask_entropy10 to53 |
| 469 | Move leaf_salt_seed12 to54 |
| 470 | Secrets(type7)51 = aggregate(move52, move53, move54) |
| 474 | Some51 into50 |
| 476 | Ok50 into49 |
| 478 | return0 = (Done48, move49) |
| 484,485 | StorageDead12, StorageDead10, with no Drop there |
| 607,613 | Drop bytes3, then return |

Outer569 false rejects and Return568; it cannot flow into success. Return
assignment478 precedes cleanup607, but caller cannot observe returned fields
until Return613. Both32 fields remain owned in return0 throughout bytes64
cleanup. Field identities come from declaration fields1 and2 and these moves,
even when all32 values coincide. StorageDead alone is not a destructor.

Root4 moves Draw.self1.request(field0) to request2; root6 moves
Draw.self1.bytes(field1) to bytes3. Root8 COPIES outcome(field2) to4 (Result
and Error here are Copy); do not describe that emitted operation as a move.
There is no normal Drop of moved-from Draw.self1 or its byte field.

Rejection has two short-circuit routes. Leaf-zero: Add380/write382 to
request2.retry precede precise Drop430(leaf12),441(field10),448(bytes3),
Return454. Field-zero: Add494/write496 precede544(leaf12),555(field10),
562(bytes3),Return568. Each compares updated retry against16 (386/500).
More moves only request2 through59 to Control58; Done/RepeatedZeroBlock has
no owner payload. No success suffix is executed after those returns.

Err arm571 copies outcome4.Err.field0 into error5;577 copies5 to9;
the From call sends9 to function2, returning Os into8. Function2's full body
(reused-glue.json) copies its value1 to2 (623), constructs Os(move2) as return0
(624), and returns627. Resume589 constructs Err(move8),591 assigns return0,
then common607 drops bytes3 before613. No32 owner is constructed on Err.
The opaque getrandom::Error representation is not proved here; no OS-world
or arbitrary-error-experiment transport follows from the copy/constructor.

Complete old owner drop_glue12 is now retained: normal Drop759 targets
(*owner_ref1).field1, Drop762 targets field2, both via Zeroizing glue15.
That glue reborrows the current owner at781, calls Drop38 at791, then
drops inner field0 through its NoopDestruct array implementation at796.
Drop38 reborrows (*self1).field0 at905 and calls the bound Zeroize at908.
No field1/field2 identity is inferred from bytes or destructor ordinal.
Unwind branches are preserved in the JSON; this argument covers normal paths.

Raw compiler drop-flag booleans are NOT in this post-elaboration LLBC. The
Move/Precise Drop/StorageDead route supports the normal ownership association;
it does not furnish the requested raw MIR flag assignments. Old054 explicitly
did not extract draw or the new run/explicit returned-owner disposal. Their
current bindings below remain source inspection pending admitted compilation.

## Current scalar hook and concrete source boundaries (inspected)

draw source has one newly initialized local Zeroizing64; its as_mut borrow is
passed to literal fill, ends on return, then the aggregate names request:self,
bytes:bytes, outcome:outcome. No child reference is stored in Draw. A native
draw witness must bind these operands and outcome on both Ok and Err; old054
does not contain it. Existing058/059 compilation is historical evidence only.

The shared run source moves draw.resume's result to a local aggregate, computes
success with a shared match, and invokes phase BEFORE moving owner out of
Some. Successful phase sees both32 fields LIVE and only bytes64 cleanup logged.
Next match moves the returned owner into owner; three typed indexing reads
copy nonce[j], owner.field[j], owner.leaf[j], THEN drop(owner) transfers that
aggregate into disposal. Old owner glue supports field1-before-field2 ordering;
the emitted run-to-glue call and its drop flags are still missing. No pointer
from the moved-from aggregate is retained or dereferenced.

Current Zeroizing::drop source lines792..800 is concretely:
coordinate(); pre=self.0.observe(j); self.0.zeroize();
record(pre,self.0.observe(j)). Each observe borrows the CURRENT (*self).0,
not a child pointer saved before draw/resume/run moves. Pre shared borrow ends
with observe before the unique zeroize reborrow; post shared borrow starts
after zeroize and ends before record. Only Copy(len,low,high) values escape.
For [u8;32/64], observe guards N and j then uses typed array indexing, byte()
dispatches array element u8 through DefaultIsZeroes to Some(*self). At32 high
is literal0; at64 it reads j+32. No pointer, cast, layout/padding or user Drop
enters an event. record writes only J-independent COUNT/E0/E1/E2/OVERFLOW;
coordinate only reads J. initialize before source owners sets j=raw_j%32.
The current source has no callback/allocation/reentry in these hooks.

The concrete relation pairs identical initialized source places, control,
request/outcome and move-initialization state outside hooks; adds ONLY those
six private statics and Copy hook locals on I. Projection forgets these ghost
values. Source draw/resume/run steps match identical instructions; each hook
must stutter on that source store. Success return field paths are precisely
return0.1.Ok.0.Some.0.field1/2, then run.result.Ok.0.Some.0.field1/2, then
run.owner.field1/2. Rejection places are resume12/10/3. These are structural
place paths within each execution, not cross-move persistent addresses.

The exact remaining primitive rule is: a temporary shared reborrow of a live
owned [u8;N] through active Drop self, read-only typed indexing producing Copy
u8, loan termination before the next mutable reborrow, and writes confined to
separate private static allocations preserve the projected source store and
enabled continuation. It must be instantiated for THESE emitted pre/post
calls, N32/64, and these precise source destination/drop sites under the
approved compiler/Kani semantics. No new generic Guard or whole-helper
equality premise is an acceptable replacement. No need to mechanize arbitrary
Rust/LLVM/hardware first is asserted. D204's existing source-plus-Kani lifetime
limits remain as stated; no retained-child-pointer or hardware-erasure claim.

This is a concrete inspected stuttering argument with emitted resume role
association, NOT an accepted mechanized native projection. The read-only2GiB
diagnostic denied admission, so no current hook MIR/borrow checking or raw
flags were obtained. Ordinary Rust under prover_rw_resume_scalar would exclude
cfg(kani) checks even if compiled; this job invoked neither.

## Final slot boundary

The unchanged paired_coordinate_native_resume target remains prepared and
uncompiled as a Kani harness, final Kani slot reserved. Structural384->12
payload reduction remains valid; no whole-formula/performance claim. The exact
next deliverable is admitted current draw/resume/run/hook MIR and drop flags,
then a concrete native paired projection validation under its supported model.
No extractor attempt is justified solely to repeat known014's projected-trait
failure. No native relation or full P6 contract was closed here. Literal
contextual successful64 E1, NativeOSWorld/error transport, actual entry/rank,
finite16, outer8 adaptive policy/durable ledger/client/full transcript and
L1/L2/L3 remain required. A ledger-after stub is not OS world. Both deployed
targets not yet established.
