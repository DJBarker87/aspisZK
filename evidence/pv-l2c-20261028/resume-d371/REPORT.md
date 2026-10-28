# D371: canonical input origins and guard follow-up

**Target not yet established. Stop: Lean budget exhausted (100/100).**
Worktree is exactly `/Users/dominic/ZK/.worktrees/pv-l2c`, branch
`codex/pv-l2c-20261028`, entry `3197fab0eb`. No frozen implementation, selected
client, release pin, wallet or account key changed. No push or deployment.

## Decisive input-origin result

No unchecked raw noncanonical limb source was found on the selected
`devnet_spend` JSON/fixture-harness route. See [INPUT-TRACE.md](INPUT-TRACE.md)
and the six `*-source-check.json` receipts. The harness does not supply a
recipient key/salt, input opening, note value or asset as JSON limbs. The
planner generates them. Its only raw M31 constructors are the final `% P`
generator and literal 77. Release-width wrapping seed arithmetic is covered.
Recipient/change owners are derived hashes of generated keys; salts are final
remainders. Every successful such owner call is proved canonical, with no
hash-success premise for the planner's eight-word inputs.

Input key/salt, pair commitments, both occupancy coordinates and inverse,
membership and super-root siblings, values, direction bits, asset, frontier
and all computed trace cells have separate bounds. Generic input validators
supply their actual success consequences; values are < 2^30 and bits 0/1.
The lane account decoder parses the root and **all twenty frontier fields**,
irrespective of active bits. Checkpoint root decoding is canonical. Address
and account/public-key codecs supply bytes, not unchecked M31 owner limbs.
The separate wallet adapter decodes output owner/salt and all input digest
fields canonically; it is not silently inserted into the planner.

Scalar/digest decoder laws retain actual rejecting branches, including encoded
P. The ordered account-field cut retains decoder calls, first-error order and
returned positions. Empty-root constants are audited. Native hash/external
binding has the explicitly listed, symbolically proved value differences and
finite same-input validation. These are per-field/source-cut results; exact
selected-planner-to-formal-carrier inclusion remains a named composition P.

`RealR1_client::prove_for_proof_accounts` accepts already compiled columns and
adds no decoder. Arbitrary direct Rust callers can still pass the D370 raw-P
case. **D370 remains valid and retained on successful canonical preparation.**
Its deciding value is the recipient's key representation; that fixed rejection
is not a demonstrated disclosure of sender-private information. On that path
there is Err(Semantic), a failed spend and no transaction. The owner's existing
choices remain decode rejection/canonicalization (frozen-code change) or an
explicit honest-domain restriction. No repair was made.

## Explicit domain and proved follow-up

`PV_L2C_ClientRoute.Transfer/Withdrawal` names the narrower canonical route:
actual outer compiler success, asset 77, output decoder/generator/hash origins,
and the ordered account-decode field cut. It models the planner's directly
constructed snapshot, not an invented call to the different 800-byte codec.
Neither original `HonestInput` nor the D370 domain was changed.

`ClientRoute.transfer_columns/withdrawal_columns` proves the exact returned
16 x 1024 C1 payload has raw words < P. This includes block pre-state and
absorption cells, permutation rows, path windows, values, occupancy/inverse,
both banks and merge. It is not only equality after field projection.

`MaterialN3.transfer/withdrawal` composes stateful sampler/fill success,
canonical mask additions, negative-sum stores, ten mask-only columns and both
d/g parser roundtrips to the complete owned base,d,g guard Result. No trace
canonicality or guard-success assumption was added. However, the execution
record must still be instantiated from the **entire native** reserve/build/
apply/derive/clone caller, including states, layouts, ownership and returns.
`guard-source-check.json` checks thirteen exact native cut bodies and retains
that missing whole-caller association. **No unconditional whole-native N3 or
observation theorem is claimed.**

N2 now has a complete owned padding-application Result. N4 has the complete
counter/rejection-control law. N5 has a structural base inverse value/zero
boundary: exact widened multiplication and reducer, symbolic fixed chain,
nonzero inverse field result, and retained panic at zero. QM31 norm/helper
association remains. N6 additionally has public node distinctness, the raw
ascending denominator recurrence and nonzero/inverse result; decoded honest
sumcheck boundary/terminal control Results pass. Actual native oracle,
interpolation arrays and running-claim transport remain P. Helper-return
composition keeps its pointwise native association premise explicit.

Both original fixtures satisfy the original honest family and the explicit
canonical-origin refinement, including lossless digest/account-field decoder
witnesses. `CanonicalFixtureDomain.both` proves non-vacuity for both. This
broader refinement is not asserted equal to the planner's deterministic
note-search/two-deposit reconstruction. The native validation cases below
likewise do not claim that exact reconstruction.

## Verification and accounting

All focused files were compiled before their dependents, privately on the
build host, one scope at a time, 6G/8G/swap-zero/Tasks64, Lean -M7000. Every
attempt's exact target, status, wall time, RSS, swap, source revision and axioms
is indexed in [RECEIPTS.md](RECEIPTS.md), with raw records in `../resume-d369/`.
Failed source/outputs are retained. No unchanged full regression was rerun.
The final new combined, fixture and focused replay targets each ran once.

| Final target | ID | Exit | Wall | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|---:|
| D371CombinedAudit | 50397 | 0 | 1.84 s | 5019103232 | 0 |
| D371FixtureAudit | 50398 | 0 | 1.72 s | 5008134144 | 0 |
| D371FocusedReplay | 50399 | 0 | 1.69 s | 5019381760 | 0 |

All three executed at `08f44c5482f9c30befd8685918e936003b09fac9`.
207 new-law axiom queries, the fixture audit and focused replay report only
propext, Classical.choice, Quot.sound. Maximum Lean RSS was 5052063744 bytes;
all swap reports are zero. The final read-only check verifies 1549 project
objects and 122 external boundary imports, with all 5673 authoritative external
objects separately hash-checked and all accepted direct dependencies unchanged.
See `CLOSE-SUMMARY.json`, `final-closure-check.json` and the retained resolution.

Optimized, capped native diagnostics (axioms N/A) are finite validation:

| Diagnostic | Exit | Wall s | Peak RSS bytes | Result |
|---|---:|---:|---:|---|
| decoder-probe1 | 0 | 14.38197 | 956878848 | 6 scalar, 48 digest boundary cases; 128 generated seeds |
| decoder-probe2 | 0 | 0.40234 | 162541568 | 512 same-input actual/owned-external hash comparisons |
| account-probe4 | 0 | 0.40230 | 178593792 | 4 lane comparisons, 4 checkpoint roundtrips, 704 raw-P rejections |
| route-probe2 | 0 | 38.90045 | 711503872 | both full compilers, 26 masked base guards/balances and actual provers pass |
| inverse-probe3 | 0 | 0.50323 | 194334720 | 131 inverse/modpow and 25 widened-product comparisons; expected zero panic |

All native swaps are zero. Each invocation/receipt pins exact executed sources,
revision, command and cgroup. Account-probe3 failed only on its diagnostic's
missing frozen-root import (0.10075 s, 17272832 bytes); route-probe1 failed only
on diagnostic include/import syntax (36.21603 s, 1159962624 bytes). Neither ran
its test body. Corrections and failed receipts remain. Prelaunch SSH255 and
refusals are retained; required 60/180-second waits and same unlaunched IDs
were used. A missing-own-import preflight before 50377 launched no compiler;
50377 was subsequently used once for its actual compile. Caps were not raised.

D369/D370 had used 3 attempts; D371 used the remaining 97. IDs 50300–50399 are
now all actually consumed: 65 accepted, 35 failed; zero remain. Historical
Lean total is 240. No new Kani; six historical invocations retain their former
status. The copy-dependent codec PASS stays suspended under K-1 and the K-2
Option<fn> quarantine remains. No quarantined PASS earns credit.

## Before/after endpoint residuals

| Row | Before D371 | After D371 | Retained P |
|---|---|---|---|
| V352 | OPEN/P, bucket b | OPEN/P, bucket b | E1/E2 streams, retries/failed prefixes, witness-independent failure/public signal, RunJoin/simE observation coupling |
| V354 | OPEN/P, bucket b | OPEN/P, bucket b | N2 whole sampler/padding caller and same-attempt geometry; stream/observation transport |
| V357 | OPEN/P, bucket b; D370 N3 counterexample | OPEN/P, bucket b; D370 retained, canonical-origin/owned N3 progress | exact selected route and whole native material/guard association; native QM31 inverse/helper and oracle/interpolation/running-claim association |
| V360 | OPEN/P, bucket b | OPEN/P, bucket b | packed-mask/column origin and full N4/N6 caller/observation/certificate transport |

Removed: zero endpoint/deployment premises and zero rows. Added/changed:
zero endpoint premises, quantifiers, observers, simulators or trust fields.
Only the explicitly named local canonical-route domain was introduced, as the
user requested; it does not repair the broader false statement. T remains
exactly entropy_law, entropy_kernel, observation. No new bad event was charged.
Existing NoPole/exhaustion conditions and failure-signal proof obligations
retain their original scope.

`HOST-CLOSE-D371.json` records no active L2C scope, 280 selected native source
hashes unchanged, removal of the 179516 KiB rebuildable Cargo cache, and
retention of the pinned Lean cache, evidence, source view and D370 nonce ledger.
No key operation occurred. [COMMITS.txt](COMMITS.txt) records the stage history
from the resume head (the final evidence-only close commit is its container).

Next concrete deliverable: instantiate the already proved `MaterialN3.Executions`
from the full frozen native caller and prove the selected JSON planner's exact
source/domain inclusion; then close N2/N4 caller geometry and N5/N6 native
associations without adding to T. The budget stop, not a new counterexample,
is why those proof obligations remain unfinished.
