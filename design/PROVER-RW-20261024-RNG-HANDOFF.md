# Owned entropy prototype: extracted control and remaining source gate

Unmerged branch `codex/cx-prover-rw-20261023`. Manager base
71100fccbd960c13cc43ba03fd4aacf39e510b34 already includes H5. Design commit
86ab10b2ce preceded code. Prototype emission commit 1466c094f3; final proof
source commit ddb833a1cd. No merge/push or native source adoption.

## Established claim

The isolated source-derived prototype replaces only the selected owner's
single fill call with an owned Draw64 provider, returned outside Result on
all exits. `rng-preflight/source-map.json` records exact original/transformed
owner/helper hashes and substitutions. The source is copied from the actual
candidate, not a generic wrapper substituted for source progress. Native
source itself has no delta against the H5 manager base.

Pinned Charon and Aeneas extract this interface into actual control carrying
`(provider,retry)` through the loop. New modules are `ProverRwRngEmission`,
`ProverRwRngNonzero`, `ProverRwRngControl`, `ProverRwRngTape` in `lean/R1Z`.
`concrete_zero_then_one` calls the emitted concrete owner on an admitted nonce
and one actual finite Tape: zero block is rejected, the next all-one block
succeeds, and the returned provider has cursor two and the unchanged reply
list/suffix. There is no owner-output premise or second independent run.
`fill_at` proves the primitive provider's actual indexed consumption.
`constant_step`, `error_state`, `cap_state` prove emitted control, including
advanced state on an OS-error tag with arbitrary partial buffer contents.
The constant-buffer OR scan is proved symbolically, not by reducing32 cells.
Tape unavailability is an assertion failure outside admitted tape executions;
it is never mapped to an invented native entropy error.

The nine audited theorem reports contain only propext, Classical.choice and
Quot.sound. `ErasureFns` exposes two unused erasure callbacks; new/deref/
deref_mut are an explicit transparent **value** installation. No physical
zeroization/drop, native provider installation or native OS semantics theorem
is claimed. The prototype error carrier is u8, not a native getrandom error
layout proof. All old obstruction and effect files remain intact.

## Same-event validation and limits

`rng-runtime-001` is an optimized **local entropy-helper** differential,
26,214 cases: both nonce admission outcomes, each rejected-prefix length0–16,
three zero/one-half-zero patterns, every u8 OS-error tag with nonzero partial
writes, success and exhaustion. It compares status/private bytes, draw count,
every freshly zeroed input, and the exact consumed ordered replies. This is
not 1,000 whole-proof equivalences and does not exercise the real cap8 owner,
body rejections, ledger duplicates or reservation ordering.

`rng-kani-002` proves an arbitrary-input **single-iteration source cut**:
nonce/full64-byte reply/error tag/prior draw count are symbolic; both original
borrowed-source adapter and owned provider return equal status/private bytes,
input/event state and updated count, including failure. The cut sets the retry
limit to1 and retains zeroization calls. It has 0/351 failed checks, unwind66,
optimized profile, exit0, wall41.41s, peak890,792KiB, swap0. This is not a
universal cap16 same-event source-owner induction. The first unwind34 check
failed in exact64-byte cleanup/memcmp loops (not memory); its source, commands,
logs and failure are retained, and the changed bound succeeds. Charon001
exited0 with an opaque owner and is explicitly rejected as control evidence;
transparent Charon002 and Aeneas001 supply the actual emission.

Regenerated externals are identified by qualified source declarations,
signature hashes and exact source-span/body hashes in `source-bindings.json`
and `adaptation.json`, never by inherited op numbers. Raw uninstalled external
axiom templates are archived as `.lean.txt`, not imported proofs. Binary
and dependency pins are hash+size only. All receipts assess the historical
host workspace label explicitly; prototype commit/source hashes supply identity.

## Unchanged assumptions and next obligation

Before: native `generate_for_mask_nonce(nonce) -> Result<Secrets,Error>`.
After in the **prototype only**:
`generate_with<P>(nonce,provider) -> (P,Result<Secrets,Error>)`.
No existing theorem premise or native API is changed. The native changing-tape
obstruction is retained; its false pure interface has not been wrapped away.

The existing OS assumption remains exactly
`ProverCommitPublicNonce40.E1` (lines44–47):
`∀ context raw, law context raw = 1 / (Fintype.card Raw : ℚ)`.
Its `next`/`run` carry schedule/error history separately. E1 is the conditional
successful64-byte return law, not a whole-owner equivalence or native world
law. This job neither discharges nor enlarges E1/E2, AeneasExtraction,
PrefixContract/BodyContract/RunJoin, bad-event laws or joint L1/L2 observation
transport. The prototype/native error-carrier association and physical cleanup
remain explicit obligations, not new assumptions.

**Next gate:** prove universal same-event old/new cap16 source-owner equality
from the retained per-iteration cut and a checked symbolic owner induction,
including arbitrary failures/rejected halves and final state. Only after that
may source plumbing extend to the actual selected callback and eight-attempt
retry owner. A native provider must implement the exact existing getrandom
boundary and retain changing state across all callbacks, body rejects, fatal
errors and duplicate durable reservations. No new source change was made
because these predecessor gates are incomplete and the Lean allocation is now
exhausted; lead review of this concrete preflight is needed before a broader
proof continuation, not approval to weaken any gate or trust item.

## Evidence, budget and artifact assessment

Canonical packet:
`docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-preflight/summary.json`.
It contains exact targets/commands, exits, time/RSS/swap, source revisions and
source/dependency hashes, full axiom reports, accepted predecessor attempts
and every failed source/log. Audit11305: exit0, wall2.14s, peak3,873,112KiB,
swap0, source ddb833a1cd (full revision resolved in summary). The final changed
Tape bridge also audits all9 theorem axioms and the complete provider/owner
signatures. No full frozen manifest was launched.

Actual new Lean launches16, including all failures: Stage3 **100/100 used,
0 remaining**. ID11292 failed dependency preflight before any compiler launch;
11289–11305 otherwise launched once, with collision checks. Kani2 actual runs:
**44/60 used,16 remaining**. No budget reset. Rust/extraction scopes6G/8G,
no swap, Tasks64; existing Lean5G/7G preserved. Launch reservations24GiB plus
7/8GiB were below55GiB. No resource failure, cap increase or unchanged resource
failure rerun. Only new ProverRwRng modules were added to joint source/objects;
no old modules or session A worktrees were altered.

All four H5 source files and the native entropy source match the manager base;
there is no crates/programs/build-input delta. Therefore no all-three-ELF
rebuild was triggered by a native change. Current f8c0/63ad/121f pins are targets,
not newly verified identities. Historical runtime/corpus/artifact evidence
remains historical. No interleaved or absolute timing ran; peer z3 PID2095724
remains present and the host is not quiet. Native integration/adoption would
still require the full event/status gates, actual differential coverage,
current all-three-ELF identities, H5-aligned <=10% slowdown and quiet-host<15s.
Candidate stays unmerged. Conjunct1 and the security target remain unestablished.
