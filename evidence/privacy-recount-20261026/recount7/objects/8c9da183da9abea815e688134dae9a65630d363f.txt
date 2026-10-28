# Recovery D356: allocation exhausted

Recovered in exactly `/Users/dominic/ZK/.worktrees/pv-l2c`, branch
`codex/pv-l2c-20261028`, from d8ce511a00. No compile, differential, Kani,
measurement, or scope was launched during recovery. Host inspection was read-only.

`RECOVERY-D356.json` lists EVERY completed Lean attempt with its receipt,
module, exit and available host completion record. It records the host artifact
hash inventory, no uncollected completed Lean attempts, no missing local compile
outputs, and no output hash mismatches. No L2C process remains active. The only
uncollected output pair was `kani-6-native/{receipt.json,out.log}`: collected
read-only and SHA-verified now. This is the already charged sixth Kani invocation
(the codec PASS), remains suspended by K-1, and receives no additional credit.
The 128-case native balancing differential's receipt/output were already local
and match the host. No unchanged work was rerun.

The resume charged exactly 72 Lean attempts: 44800–44868 and 44897–44899,
55 passed, 17 failed. Earlier work charged 68 Lean and six Kani invocations.
Totals: 140 Lean, six Kani. Remaining authorized resume budget: ZERO Lean and
ZERO Kani. Reservation refusals charge zero. No out-of-block ID was used.

Recovered valid uncommitted evidence includes the 44868 source/receipt/output,
its batch metadata, final audit batch metadata, updated source resolution and
structural-binding record, and final closure check. They are retained and
committed with this handoff. No uncommitted proof-source edit required a compile.
The final accepted proofs were already committed before their receipt collection.
`commits-from-base.txt` records the requested base-to-head history before this
recovery evidence commit.

The corrected-public-import final audit 44897, exact-carrier fixture audit
44898, and focused replay 44899 all passed; their raw receipts record source
revision, source hash, dependencies, wall/RSS/swap and every printed axiom.
Only propext, Classical.choice and Quot.sound occur. Final closure check covers
1456 objects with no failures and matching toolchain. This is the focused local
closure, not a full frozen endpoint release replay.

Proved progress includes exact HonestInput caller/returned-bank transport;
decoded honest helper total and inactive sums; honest validity under existing
NoPole; decoded sumcheck boundaries; complete extracted scalar/QM31 parsers
on canonical words; complete owned scalar/Q balancing Result laws and scalar
canonical output preservation. Both original fixtures, including the concrete
field instance, are audited. Structural (K-1 substitute) binding is limited to
the balancing cuts and does not establish native caller or trace refinement.

V352/V354/V357/V360 remain OPEN/P bucket b. Zero endpoint/deployment premises
removed, added, weakened or changed; trust fields unchanged. No checked honest
input with an unexpected guard branch was found. Target not yet established.
Next deliverable: raw native compiler canonicality through the returned bank,
then sampler/padding/caller geometry transport; native helper inverse and
oracle/interpolation/running-claim associations and E1/E2 remain obligations.
Stopping reason is the expressly permitted compile-budget exhaustion.
