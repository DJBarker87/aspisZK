# Current scalar source/MIR relation and exact limit

This closes the requested current source/MIR role-association obligation only.
It is an inspected normal-path projection argument, not a mechanized native
relation, complete P6 instance, OS law or privacy result. Before = after: the
complete signatures, carriers, quantifiers and normal outcomes in
../resume-p6/SOURCE-CONTRACT.md. No theorem statement/premise changed. No trust,
freshness, independence or error law added; no cryptographic or native premise
is discharged by ordinary compilation. Old054's corrected success association
is accepted reused inspection; it was neither reopened nor re-extracted.

## Exact current inputs and compiler scope

The five proof files, metadata, instrumented/original zeroize and error source
snapshots are copied verbatim from final resume-scalar. Package identity retains
unchanged registry files except the specified instrumented lib/error and the
original zeroize package name. These are prospective private source copies,
not shipped crates. pin-summary.json binds source revision ac5614d248, all
50,077 pre/go/post file hashes (identical), full inventory fingerprint and
oversized remote records by hash/size. source-identity.json binds local final
copies and the inspected P6/tool interfaces. No newer artifact identity gate
is attributed to old evidence or the three manager ELF pins.

Compiler rustc1.93.0-nightly53732d5e0, LLVM21.1.5, host x86_64 Linux. Its
.kani toolchain path is a symlink to .rustup/toolchains/nightly-2025-11-21-
x86_64-unknown-linux-gnu, the sysroot returned by the postrun read-only
--print sysroot query. The ENTIRE symlink-target tree was already enumerated
and file-hashed before/go/post through the .kani path; the later path query is
explicitly postrun metadata, not a retrospective compilation/check.

One cargo rustc --offline --locked --release -j1 --lib -- --emit=mir, with
RUSTFLAGS '--cfg prover_rw_resume_scalar -Ccodegen-units=1 -Zdump-mir=all
-Zdump-mir-exclude-pass-number -Zdump-mir-dir=<own stage>/mir'. This includes
ordinary dependency compilation. It does NOT set cfg(kani); checks module and
error's kani-only representation constructor are excluded. No claim that the
paired harness was typechecked. All-pass dumps requested together avoid a
second compiler invocation. 132 selected complete textual MIR files retain
built/NLL/drop-elaborated/optimized forms and glue including cleanup blocks.
The full143929-file dump inventory is24,860,509B: hash+size only locally.

## Actual source places, moves and emitted drop flags

References below use Instrumented ElaborateDrops.after.mir unless specified;
association.json and inspect.py pin exact operands and blocks. Original forms
are retained separately. No identity uses bytes, ordinal or persistent address.

Draw bb0 initializes _3=[0;64], moves it to Zeroizing.new -> owner_2.
bb1 borrows _2 through _7 into as_mut -> _6; bb2 reborrows _6 as _5 and
calls literal fill once into outcome_4. bb3 ends _5/_6 storage, moves request1
into8 and bytes2 into9, copies outcome4 to10, and constructs return0 with named
request/bytes/outcome operands. Both Ok/Err use that same aggregate; there is
no outcome filter in draw. NLL bw0 region'?2 covers bb1[6..=7],bb2[0..=2];
bw1 region'?3 covers bb2[0..=2], ending before bb3's move. draw's bb6 cleanup
drops bytes2 if as_mut/fill unwinds. Normal moved-from drops are eliminated;
there are no raw boolean drop flags in this emitted draw to reconstruct.

Resume bb0 moves self.field0->request2, self.field1->bytes3; self.field2 outcome
is COPIED to4. Err bb3 copies4.Err.0->7->12, calls From into11, bb4 constructs
Err11 and return0. From's complete current MIR constructs Os from its input;
no arbitrary error/OS experiment transport follows. No32 owner constructed.
Err and success join bytes64 drop bb42 before return44. On Ok, owner13 is
field_mask_entropy and15 is leaf_salt_seed, initialized in that order and filled
from range ..32 and32.. of bytes3. Successful tests route bb21: nonce2.0->57
Copy, field13->58 Move, leaf15->59 Move; Secrets56 names those fields; bb23
Some56->55, bb24 Ok55->54, bb25 return0=(Done53,54). bb26->40->41->42 has
StorageDead15/13 and NO32 Drop; both fields remain live in return0 throughout
bytes3 cleanup. These statically resolved paths retain NO boolean drop flags.
Rejection routes bb29 AddWithOverflow/retry write30, then More31..33 or
exhausted34..35, before normal Drop15 bb36, Drop13 bb37, Drop3 bb38. Entry0..15
makes retry+1<=16, but ordinary compile does not prove controller reachability.

Run draw->8, resume->12; bb2 moves control12.0->10 and result12.1->11.
bb8..12 examines &result11 via23; bb12 ends23 then calls phase(success) BEFORE
bb16 moves11.Ok.Some.0 to owner35. phase is an arbitrary function parameter in
ordinary run; the paired harness's actual phase assertions remain cfg(kani).
Success fields are therefore live at that call on a normal return from phase.
bb20 copies nonce35.0[j]->37; bb22 copies field via41->40; bb24 copies leaf via46
->45; constructs Owner projection36 and ends41/46 storage BEFORE35->51 Move
and explicit mem::drop51. Source j<32 is supplied by the prepared harness;
index-panic cleanup is retained, not erased from the claim.

The emitted run flags are exact:54/55/56/57/58 initialize false in bb0;
54/55/56/58 true at result initialization bb2; bb16 sets58 false and57 true
before result payload->35; bb24 sets57 false BEFORE35->51; bb26 sets57 false;
bb28 clears54/55/56/58. Cleanup bb66 tests57 to drop35 at65; bb70 tests58 to
drop11.Ok.Some.0 at69.54/55/56 retain other elaborator scaffolding; no invented
owner identity is assigned to them. Full statements and cleanup routes remain.
Struct glue AddMovesForPackedDrops.before bb7 drops field1 then bb6 field2;
Zeroizing32/64 optimized glue freshly reborrows its CURRENT owner and calls
actual Drop. No moved-from source is observed; StorageDead is not a destructor.

## Typed hook projection, normal paths

At a hook boundary relate identical original/instrumented source control,
initialized live source places, move-initialization state, actual primitive
outcome and source continuation. Instrumented side additionally has J/COUNT/
OVERFLOW/E0/E1/E2 and temporary Copy scalars. Projection forgets just those
extra allocations/scalars, not the source byte owners, outcomes or cleanup.
This is an explicit candidate operational relation, not an assumed equality
of helpers/results. Source moves update corresponding destination places in
both executions; no address is required to persist across a move.

Current Zeroizing Drop Elab bb1 creates shared4=&((*self1).0:Z), calls observe
into Copy Observation3; bb2 ends4, creates unique7=&mut((*self1).0:Z), calls
actual Zeroize; bb3 ends7, copies3->9, shared11=&((*self1).0:Z), calls observe
into10; bb4 ends11 and passes only observations9/10 to record. NLL borrows:
bw0 '?3=bb1[3..=6]; bw1 '?4=bb2[5..=6]; bw2 '?5=bb3[7..=10]. They are
nonoverlapping temporary regions beneath active self. This compiler region
output supports the source loan argument, not an accepted aliasing theorem.
Optimized Drop keeps the same pre/mutable/post ordering, inlines coordinate
and record, and retains actual Zeroize as a call. No assertion of LLVM machine
behavior, physical/register/cache erasure or concurrency follows.

Array observer's complete MIR guards N in{32,64} and j<32 before indexing;
low is &self[j] -> Zeroize.byte -> DefaultIsZeroes.byte(u8) = Some(copy *self).
When N64 it additionally uses guarded j+32; when N32 high is literal0. Each
successful call returns Observation{len:N,low,high} with no reference. These
reads do not write source arrays; index/AddWithOverflow panic branches are
retained. For initialized N32/64,j<32 the guards entail index<N and j+32<64,
and u8 always Some; no sentinel branch executes. This is direct symbolic
source reasoning for these sizes, not another Nat wrapper or generic Z law.
The original scalar volatile-write/fence/iterator/array Zeroize remains the
matched payload-changing computation. Hooks do not substitute zeroization.

Current record's emitted allocation map is alloc6=COUNT,7=OVERFLOW,8=E0,
10=E1,12=E2 (IDs scoped to this dump). Only these static pointers are written;
coordinate reads alloc5=J in optimized Drop. These are named separate compiler
static allocations, never derived from the source self/array pointer. record
copies observations into Event, switches COUNT0/1/2 to corresponding event
and literal count1/2/3; other COUNT sets OVERFLOW. No callback, allocation,
source owner field write, index, increment or destructor enters record.
Compiler dumps display Event padding, but the observer never reads padding;
only typed fields are copied/compared, with no byte-layout premise. Event and
Observation have only usize/u8 fields and Copy derives; no live source reference
can be stored there. Source selected/observe modules name no private statics.

Thus the concrete added normal-path segment consists of temporary typed shared
reads, Copy scalar computation, and stores confined to those separate statics.
Under the accepted native model's rules for THESE operations its projection
stutters and enables the same unique Zeroize continuation, then stutters again
on the posthook. The source/MIR associations now identify every relevant active
Drop self and return/run destination. This finishes the inspected argument;
mechanized concrete validation of that projection is still the next producer.
Nothing demands a general Rust/LLVM/hardware semantics as prerequisite.

Normal source census: Err64 only; reject leaf32,field32,64; success64 before
return, then explicit owner's field32/leaf32 disposal after phase. Therefore
1 or3 observations fit the three static events. No event ordinal is used to
identify which owner was dropped. Complete built/NLL/Elab/optimized unwind and
panic branches are retained; their paired relation is not established.

## Literal existing rule and why it is not a producer

Read complete BuilderDropObservation.lean including P6Route, not just its name.
Its exact field is:

    specification : ∀ memory, sourceDrop memory = dropSpec owned memory

with Memory=Nat→U8; dropSpec owned memory=ok((),wipe owned memory). p6_outputs
requires that certificate plus ∀j∈output,j∉owned and proves the output bytes
unchanged by sourceDrop. wipe_frame/wipe_observation prove the HEAP MODEL's
frame rule. There is no typed-reborrow/Copy/static-store native source instance
for this scalar hook in that module. Supplying the desired sourceDrop equality
would hide the missing producer, so no instance or premise has been introduced.
BuilderRecordsP6.Route similarly contains FieldsEqual for unrelated builder
records and cannot serve as the actual entropy helper source producer.

The previously accepted native-owned-drop Kani049/050 checks are REUSED
component context only: moved initialized Zeroizing32/64, actual drop once,
fresh root after drop and untouched16-byte frame arrays under Kani's model.
They do not contain these current typed hooks, record statics, run/phase or
this selected helper. ProverRwRngNativeEmission's NativeTypes/ErasureFns and
Zeroizing value aliases/transparent constructors do not prove physical Drop;
its ErasureFns callbacks remain explicit. ResumeScalarCoordinate/Capacity are
only natural-number bounds/extensional facts. NativeDropABI moveSwap relation
is an unrelated generic permutation model. None is a concrete native producer
for the present hook; no Lean compilation is justified by these interfaces.
Known014 rejection remains retained; no new extraction/backend attempt.

The exact next validation target is the already prepared same-input paired
checks::paired_coordinate_native_resume, actual draw/resume/run and hooks under
accepted Kani memory model, after lead review/allocation. Its source is now
synchronized to the new stage, but cfg(kani) has NOT compiled or run here.
MIR readiness is improved, not final-slot proof readiness or authorization.
The final Kani slot stays reserved. The boundary stub's LEDGER-after is not
OSWorld. Literal contextual successful64 E1, NativeOSWorld/error-law transport,
actual controller entry/rank, finite16, outer8 adaptive public policy/durable
ledger/full transcript/L1L2L3/client and every adoption gate remain unchanged.
Both deployed targets not yet established.
