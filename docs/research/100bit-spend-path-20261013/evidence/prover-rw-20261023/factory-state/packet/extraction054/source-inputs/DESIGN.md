# ProverRwFactoryState: owned request/resume candidate

UNADOPTED. Design revision starts at dc26b384f5. No production source edit,
extraction result, native theorem or probability transport is claimed here.
This design replaces the FactorySource pure-helper interpretation, not its
retained source or failed admission evidence. D187/D191 authorize only a gated
host candidate. No protocol, verifier, feature, wire or trust change.

## Concrete source boundary (commit before implementation)

Before: generate_for_mask_nonce(nonce32) -> Result<Secrets, Error> performs the
zero-nonce guard and the whole sixteen-draw loop. The rejected prospective
one_draw(nonce32,retry) -> Result<(retry,Option<Secrets>),Error> has no carrier
for successive primitive outcomes or advancement on Err.

After public API: identical. Private owned controller:

* start(nonce32) -> Result<Request, Error>, with Request { nonce32, retry }.
  It rejects zero before allocating or filling a buffer.
* Request::draw(self) -> Draw, the NATIVE EFFECT boundary. Draw owns the same
  Request, a real Zeroizing<[u8;64]> initialized to zero, and the literal
  getrandom::fill result. The fill is executed exactly once. Draw is returned
  even on Err, so postbuffer and control ownership are outside Result.
* Draw::resume(self) -> (Control, Result<Option<Secrets>, Error>). Control is
  More(Request) or Done. This is the DETERMINISTIC selected extraction target.
  It consumes the actual returned buffer/result, maps the identical Error,
  creates field32 then leaf32 only on Ok, copies the same halves, applies the
  identical short-circuit guard, moves successful owners or increments retry
  before lexical leaf32/field32/bytes64 drops. Rejection sixteen returns Done
  with RepeatedZeroBlock. Earlier rejection returns More with Ok(None).
* Native driver loops over More; it never interprets draw as a fixed pure
  callback. It returns success/error directly and does not prefetch a draw.

This is a changed real implementation proposal, not another duplicate proof
cut. The selected preflight will contain the complete called driver and types;
Charon starts at Draw::resume, including its deterministic dependencies and
real cleanup. No opaque whole-helper contract. No trait, generic Guard, logger,
stub, forget, leak, unsafe or drop_as_no_op. Native Draw carries actual effect
data; retry is a control index only, never evidence of OS freshness. No pending
buffer may be cloned into a tape or retained after resume. Additional moves
and changed drop locations remain native/P6 obligations, not compiler folklore.

## Weakest proposed sufficient relation

Native operational state (owned Request/Draw/Control and live allocations)
and abstract OS world W are distinct. Relate an execution by an ordered list
of primitive outcomes, including every fill entry, initialized input, full
postbuffer on both Ok and partialErr, exact NonZeroI32 error representation,
and actual before/after world transition. Also retain semantic owner moves,
cleanup provenance/order and the surrounding public/ledger/error events.
The native draw leaf must produce this relation at the literal call site;
neither a counter nor a chosen response list proves it. No full equality of
OS states is required: a relation R may connect distinct worlds when each
reached primitive transition preserves R and the required event projection.
No acceptance/output-equality premise substitutes for those local obligations.

Sufficiency argument to mechanize: induction on remaining draws, splitting
the actual primitive outcome. Err stops with its exact error and post-world;
Ok/nonzero stops with the exact two owned halves; Ok/zero increments retry
and composes the same transition/event prefix with the induction hypothesis.
The zero-nonce base consumes no event, and sixteen rejections exhaust. An
outer induction must then preserve arbitrary mutable PUBLIC proof_account,
its calls and returned nonces, all eight retry branches, ledger operations,
errors and cleanup; identical public history allows the same adaptive policy
step. This deterministic all-outcome argument does not establish privacy.
It is presently an argument/design, not a compiled theorem or source relation.

For probability transport, event projection must identify the successful64
carrier with literal R1Z.ProverCommitPublicNonce40.E1, forall context raw,
law context raw = 1 / card Raw. Context may contain the whole earlier history.
E1 and L1/L2/L3 remain explicit/open. No new independence, freshness,
uniformity, witness-independent retries or whole-output assumption is added.
The concrete native transition/P6 producer and event transport must be proved
before this proposed relation can be used; a record of obligations proves none.

## Preflight and bounded gates

First generate a complete prospective full-file snapshot and exact before/after
statements, checking the immutable production input. Then Charon precise built
MIR of the selected resume declaration; only if credible use existing unaccepted
candidate014 with real Drop evaluation, without emitted-Lean edits. Inspect
complete declarations, externals and drop graph. An unsupported actual type or
declaration stops this path; isolate it rather than pursue a backend campaign.
No generic96 migration, invariant/full-BMC retry or duplicate cut.

Extraction ceiling56, entry52 charged; four available, charged even on guard
failure, with actual invocations separate. Backend15/16, Lean236/260,
Kani57/60 unchanged; at most two Kani and last one reserved. Rust0/3 and
ELF0/3 carried forward. No Lean or Kani launch is justified before extraction
credibility. No full manifest. Focused extraction scopes ONLY: High1536MiB,
Max2GiB, Swap0, Tasks64, fresh before/go corrected all-hierarchy admission,
finite reservations strictly below55GiB and additional resident+7GiB check.
Read-only formula diagnostics precede compiler reservations; one correct denial
ends launches. Include sysroot rlibs/toolchain/binaries/dependency/source hashes
before/go, captured stderr/time even for denial, and N/A axioms for extraction.
Preserve prior052 and all original source inputs unmodified.

Only supported source/P6/effect progress justifies applying the authorized
state_only_entropy.rs edit (selected retry-owner sites only if necessary).
Any crates edit requires fresh all-three ELF gates at current pins and focused
optimized checks. All native refinement, outer8, E1/L1/L2/L3, selected client,
whole-prover fixedcoin1000/proof bytes, quiet median<15s and slowdown<=10%
adoption gates remain. Both deployed targets not yet established.
