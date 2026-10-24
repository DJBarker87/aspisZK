# Prospective helper/controller association: no production relation established

Production remains the immutable original. The proposed full-file snapshot is
NOT installed or called by crates/aspis-prover. `source.py --check` checks the
original bytes against factory-iteration/production-source.txt and056's exact
cut hash. source-map.json includes complete before/after controller and helper
statements, byte span/hash, and full prospective file hash. The selected
preflight crate contains the new controller actually CALLING the private helper,
but no compiler/extractor reached this crate. This is source design/association
of a prospective edit, NOT native, extracted or semantic source progress.

## Complete interfaces and ownership changes

Before public `(nonce32) -> Result<Secrets, Error>`: nonce guard; retry0; while
retry<16; zero64/fill?; zero32 field then leaf; copy halves; nonzero conjunction;
success moves both32 into Secrets; rejection increments retry before drops.
After public interface identical; helper `(nonce32,usize) ->
Result<(usize,Option<Secrets>),Error>`. Complete textual statements are retained
in source-map.json rather than hidden inside a contract structure. Controller
propagates helper Err with ?, returns Some owner, assigns retry on None.

Helper executable body is056 byte-for-byte except public->private visibility.
On Err bytes64 drops before propagation. On success field32/leaf32 move through
Self/Some/tuple/Result; bytes64 drops before helper returns; caller match moves
the same owner into public Result. On rejection retry+=1 precedes lexical
leaf32/field32/bytes64 drops; only afterward does the controller receive and
assign the retry. Extra aggregate/return/match moves are explicit semantic
obligations, not proven by matching the helper body or presumed optimization.
No wipe guarantee for stale moved copies, registers/caches, or unwind/abort.

## Existing P6 boundary does not prove this new opaque interface

056 universally quantifies nonce32, entry0..15, initialized postbuffer64,
Ok/Err selection, custom-u16 Error, and ghost u64 advancement. It checks exact
normal Result owner bytes, nonce, retry/success/rejection. It invokes real
Drop/fence, but does not expose a cleanup-event/provenance relation. Reused
owned-drop049/050 cover retained-storage initialized payload/frame under
sequential Kani/P6; they do not prove this helper's control-site invocation,
order, count, lifetime or unwind transport. No generic whole-helper event
contract may be inferred from these distinct carriers and frames.

The prospective Charon command would make ONLY one_draw opaque in its LLBC,
not in Rust. Its Rust result signature contains neither world-after-on-Err
nor frame/event output. A plain pure callback of (nonce,retry) cannot produce
arbitrary successive OS results across repeated equal arguments: fix any
nonzero nonce and retry0; two permitted OS histories return different nonzero
halves (or one returns partialErr), while one fixed callback returns one value.
An indexed tape can describe one finite trace, but the source association and
actual advancing OS/E1 producer across arbitrary outer8 adaptive policy remain
unproved. Ghost retry/provider tokens cannot supply that producer. This is an
interface assessment/counterexample to a proposed PURE interpretation, not a
new theorem, not an extractor rejection, and not proof that fission is impossible.

Error coverage is also narrower than the requested leaf: getrandom0.3.4
error.rs represents non-UEFI Error with NonZeroI32; new_custom(u16) covers
131072..196607 only. Internal UNSUPPORTED has65536; negative OS codes are
another disjoint class. Thus056 does not even cover all public Error constants.
No immutable constructor extension or all-representation Kani check ran.

No Aeneas output was generated, so there is no fresh opaque/external/Drop graph
to audit. The earlier049 graph (factory-cleanup association document) retains
generic Zeroizing glue, projected Drop and Iterator::next Option<&mut T>. Prior
candidate014 rejection is reused only as historical evidence for those EXACT
inputs, never relabeled as failure/success of this prospective controller.
The planned candidate014 is unaccepted; neither P6 nor AeneasExtraction silently
adopts it. No new cleanup/extraction/trust assumption is introduced.

## Claim and required next native producer

Established: checked prospective text factoring and immutable056/source/library
association, plus retained failed resource admission data. No premise changed;
all original theorem statements/hypotheses remain identical. No finite16 actual
controller normal-outcome theorem, universal-error law, cleanup-event theorem,
OS/world transport, E1 law, or binary identity was established. No newly compiled
Lean theorem; full #print axioms N/A.

Next: resource-reviewed supported extraction of the REAL fission controller,
with an explicitly reviewed small leaf contract whose carriers/frame/events
and Err-state advancement match an actual helper proof. The opaque signature
above cannot simply be declared to have those missing properties. Only after
that preflight is credible apply the authorized private helper edit, then run
factory checks/timing and all-three-current-ELF rebuilds. Do not add another
duplicate proof-only cut or resume the stopped invariant/full-BMC method.
