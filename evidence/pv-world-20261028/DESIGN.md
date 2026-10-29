# World interpretation: contract and boundary audit

Target not yet established. This document distinguishes proved calculus from
proposed installation. No privacy-ledger row is closed by defining an interpreter.

## Where threading enters now

`PV_RunJoin_TrustItems.lean` defines `TrustBoundary.Observation` with initial,
calls, final, filesystem and payload. Each calls element is `(preWorld, Call)`.
The Call constructors are entropy, file, time and worker. File/time/worker
constructors carry their next World; entropy carries its index and reply.
`OsWorld.World` has exactly entropy/entropyUsed, files/fileUsed, time/timeUsed,
workers/workerUsed. These are tapes/cursors, not an allocator or a concrete
filesystem. `fileStep` matches the request at the cursor and advances it once.
The separately stored `Observation.filesystem` is `ProverCommitLedger36.State`.
It is not a field of that World. Neither record enforces trace continuity.

`TrustEndpoint.trustData` copies the event fields from the freely supplied
nativeEvents/extractedEvents functions. `complete_view` uses congrArg payload
on T.observation, then the independent P.trace equality. It does not construct
extractedEvents or check that their calls were executed. `TrustModels.model`
can choose the same arbitrary observation for both sides; satisfiability is
not native adequacy.

`CallerWorld.execute` threads the entropy Tape through the specialized
retrying caller. Boundary.draw is a Draw64 Tape, expressly not the world-free
getrandom callback. The ledger wrapper `LedgerWorld.reserve` executes the
world-free source reserve under one `ops`, then updates the modeled ledger
on an outer successful Result. Its `source_projection` proves erasure back
to that source Result, not the native file effects or an OS trace.

The frozen `ProverRwFullExternalFuns` fields op4/op14/op15/op22/op23/op122/
op123/op261 return Aeneas.Result and accept no OS World. In `reserve_fallible`
(lines 14439–14526 of ProverRwFullFuns), the same instance supplies path/options,
open, three writes, file sync, directory open/sync, and error decoding. File
values can be returned from write_all, but the file-event cursor is never an
argument/result of these callbacks. Choosing `ops initialWorld` once does not
choose `ops currentWorld` at each call. This is the shared D363 obstruction.

## Calculus proved in PV_W_Threading

`M W C E A = W -> Run W C E A`, with Run containing Outcome (ok/fail/div),
post-world, and ordered `(pre-world, tag)` list. bind appends the continuation's
trace and passes it the preceding post-world; failure/divergence retain their
prefix effects. This is a denotational partial-execution representation:
`div` records a finite observable prefix, not a theorem that all infinite
native executions have finite traces.

liftCallback embeds every world-free function and lift_frame/lift_bind prove
its frame and composition laws. These are universally quantified mathematical
facts. They do not certify that a Rust callback is genuinely pure. In particular
op4 is not classified pure generically. op23 can use a pure lift only after
its complete Error representation/decoding law is proved. All other dictionary
entries require their existing row laws and native correspondence before being
classified pure. There is no blanket proof of native purity in this stage.

Threaded expresses continuity. valid_emit is the one-call rule and valid_bind
is the named caller-composition rule, for every Outcome constructor. These can
be instantiated at the exact existing World and Call types without a change
to their definitions. Such an instantiation alone would still not be a theorem
about the extracted prover. no_lift_advancing and no_trace_decoder delimit the
post-evaluation lifting approach; a syntax-directed interpretation retaining
calls before evaluation is necessary for the requested repair.

## Proposed installation, not a proved implementation instance

A syntax-directed sidecar must interpret the frozen caller's lets, matches,
error returns, loops, and callback sites, with one named correspondence lemma
per function. Its judgment must relate the emitted source expression, current
World, return Outcome, post-World, and ordered tagged calls; the World argument
belongs to this judgment, not a new T field. It cannot be only a function of
the source's already evaluated Result.

Use existing fileStep/timeStep/workerStep and an entropy step that checks
entropyUsed = i, reads entropy i, advances entropyUsed, and emits entropy i
reply even on OS error. Exhausted/mismatched tapes are interpreter failures,
not successful no-op OS calls. Distinguish the outer interpreter Result from
the nested native io::Result. Each syscall consumes an event even when its
native reply is an error. Error paths retain all prior effects.

Allocator and memory semantics need additional **P data**, including live
allocation identity/size/alignment/capacity/content, ownership, volatile-write
history and ordering/fence state. The current Observation World has no such
fields; current Call has no memory-effect constructor. Two possible designs
are an enriched interpreter state `(OsWorld, MemoryWorld, LedgerState)` plus a
proved projection to the unchanged Observation, or a proved adequacy quotient
showing which memory state is already determined by the extracted values and
D159 payload. Neither has been installed. Hiding memory effects in the
entropy/time/file tapes would change their documented meanings and is not a
repair. A proposed enriched state is not an extra trust field.

For every memory operation require explicit error, post-memory, ownership and
frame laws. For zeroize require restoration of each mutable write, volatile
writes of the default-zero representation, and fences; value equality alone
is insufficient. For drop require the actual reached type's destructor and
unwind/nonreturn behavior, including implicit file closes on early returns.
The frozen sync_directory/reserve bodies contain no explicit File close at
scope exit, so a sidecar also needs a justified lifetime/implicit-Drop rule;
translating only their written callback sites cannot produce that close tag.
This observation is a source audit, not a new native counterexample or a
universal impossibility result for sidecar semantics.

To finish caller-level exactness: prove each primitive step's tag/next-world
law, compose through all branches with valid_bind, and separately prove that
the constructed extracted observation has those exact fields and full D159
payload. Prove filesystem projection agrees with the interpreted ledger,
including post-error partial effects. Then use T.observation to transfer it.
Using that trust equality to justify the primitive steps would be circular.

## D364 resume: checked implementation of the source-stage design

The historical "proposed" subsections above describe the initial stop state.
The resume supplies `PV_W_Enriched`, typed syntax, exact reservation reification,
source erasure, operational execution correspondence, typed primitive arguments
and algebra, explicit error embedding, and tape interpreters over the EXISTING
OsWorld. File, entropy (including error replies), time and worker steps retain
pre-world tags and explicit filesystem/process updates. A tape/configuration
fault is distinct from a native IO error value. Value-only model decoding
retains prior effects on errors/divergence; no native decoder purity is assumed.

`PV_W_OsCombined.reservation_full` and `.reservation_os` compose the typed frozen
reservation with these relations and project internal process steps only when
OS framing is proved. `PV_W_RepeatFile` represents the retained repeated-create
outcome shape with a genuinely advancing shared tape and full ordered trace.
Neither the tape nor its arbitrary update DATA proves OS semantics.

`PV_W_ProverEntry` additionally reifies the exact emitted prove_masked_attempt
entry (16 call sites), with complete-Result erasure and ordered operational
composition. Its prove_masked_with_attempt call remains a helper subprogram;
it is NOT a theorem about that helper's internal external calls or the whole
retrying prover. Remaining helper thunks are not declared genuinely pure.

The sufficient concrete native process representation, primitive/helper
adequacy, implicit Drop/close, native filesystem/error carriers, whole-prover
control-flow coverage and complete D159 Observation/deployment binding remain
unproved. In particular the new projection theorem is not silently substituted
for the required existing Observation producer. No T field, observer, simulator
or privacy premise is changed, and no row is closed.
