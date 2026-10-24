# Prospective request/resume source: exact boundary and obstruction

No production source was changed. `source.py --check` verifies the immutable
production bytes against the retained original, and source-map.json contains
the complete before/after public method and all new private types/methods.
The design was committed in9801aabe0b before implementation737753b9ac.
There is no new theorem, changed theorem premise, native source contract or
whole-owner output equality assumed here. Full #print axioms is N/A.

## Complete new carriers, not a pure OS callback

Request owns nonce32 and retry:usize. Draw owns Request, a real
Zeroizing<[u8;64]> and Result<(),getrandom::Error>. Control is More(Request)
or Done. Resume consumes Draw and returns (Control,Result<Option<Secrets>,
StateOnlyAttemptEntropyError>). The native driver calls start, then the
literal Request::draw (zero64 and getrandom::fill), then resume until terminal.
The public signature remains nonce32 -> Result<Secrets,Error>.

For the proposed deterministic resume interpretation, repeated equal
(nonce,retry) no longer forces the same primitive outcome: the input explicitly
contains the actual initialized postbuffer and exact primitive result. A native
draw is STILL not a pure function of Request. It must remain a transition of
the external world W; it was deliberately not selected for pure extraction.
Returning Draw even on partialErr keeps that pending native effect and its
postbuffer outside Result before resume consumes/cleans it. Control::Done after
Err is not a representation of OS world-after, a fresh token or a proof that
the OS state advanced. The required native event/world association remains
unproved, including retention through all outer8 continuations and terminal
errors. No reset retry counter is identified with OS freshness.

The source sketch retains the nonce guard before buffer initialization/fill,
one literal fill per draw, the source Error From, real Zeroizing/Drop, field
then leaf construction, identical halves and short-circuit guard, owner moves,
and rejection increment before lexical drops. At rejection16 it constructs
RepeatedZeroBlock before cleanup; the original constructs that variant after
loop cleanup. Result delivery remains after cleanup, but this plus extra
Draw/destructuring/return moves is an explicit source/effect equivalence
obligation, not a theorem or a claim about stale moved storage. No logging,
destructor replacement or instrumentation erasure is presumed.

## New extraction and actual unsupported declaration

Extraction054 selected ONLY ProverRwFactoryStateDraw::resume (function0),
with precise built MIR and included unchanged zeroize1.8.1. The compiled crate
also contains the complete called prospective native driver; that driver's
OS calls/outer owner were not extracted or proved by this selection. The
full expanded selected signature/body, types/traits and dependency signatures
are retained in emission-audit.json. No emitted Lean was created or edited.

Function0's normal Drop sites430/441/448 and544/555/562 correspond to the two
short-circuit rejection paths (leaf32/local12,field32/local10,bytes64/local3).
Common normal return Drop607 is bytes64. These are syntactic sites, not a
verified dynamic event count, cleanup order or erasure theorem. Their target
is regular Zeroizing glue15. Its normal Drop796 and unwind Drop786 address a
projected generic inner field and use a trait fn_ptr, not a regular target.
The graph also retains Iterator::next130 returning Option<&mut T>.

The pinned014 PrePasses source hashes to the exact source hash in its reused
build receipt; its binary hash is freshly checked in054's preflight/go pins.
`lower_precise_local_drops` supports ONLY PlaceLocal/FRegular/Precise and
explicitly raises on all other Drop shapes. `shape-check.py` checks this exact
source branch and the actual emitted dependent Drop796, and identifies seven
unsupported syntactic Drop sites overall. This is new READ-ONLY static
compatibility evidence, not an actual Aeneas rejection/run, backend acceptance
or a new identity proof. Existing014 remains experimental/unaccepted;015 was
not used. No new trust or backend campaign is justified.

## Sufficiency and smallest next producer

The ordered-primitive-outcome relation proposed in DESIGN.md remains to be
proved. Native storage/control and W are distinct. A successful native leaf
must associate the exact zero64 entry, Ok/partialErr postbuffer, exact error,
cleanup/frame/provenance and ordered world transition with the native call.
An arbitrary response list, accepted result or identical owner bytes cannot
produce this fact. E1 must remain the literal successful64 law in
R1Z.ProverCommitPublicNonce40 with arbitrary history context. No independence,
freshness or witness-independent retry assumption is added.

Smallest feasible follow-up is a concrete source/P6 contract for this OWNED
resume/driver boundary with all valid NonZeroI32 errors and real caller Drop
events, plus the primitive/world transition association. Prior056 supplies
only its different cut/custom-u16 normal relation and cannot instantiate this
contract. A safe cfg(kani)-only constructor may cover the error carrier, but
it alone proves neither cleanup nor world transport. No such constructor or
Kani check ran here. Generic projected-drop/loan support stays failclosed.
Do not replace this with a new duplicate cut or the stopped invariant/BMC path.

Finite16 normal/effect composition, outer8 arbitrary mutable public policy,
selected-client/ledger/error connection, native cleanup, E1/L1/L2/L3 and
probability transport all remain open. The concrete native producer above
must precede any production edit, ELF acceptance or privacy claim.
