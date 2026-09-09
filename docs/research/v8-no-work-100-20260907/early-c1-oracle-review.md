# Early C1: causal lazy-oracle target bound

Status: **formal proof complete for the explicit finite oracle model;
actual Rust/Fiat–Shamir coupling remains open.** Research only. The new work
reuses V7's generic adaptive-target counting and actual SHA-256-prefix
projection theorems; it does not reuse V7's q16 call budgets.

## New result and its implication

For an arbitrary fixed early full-answer prefix and C1 root, let `S` be the
previously constructed set of first-unresolved targets over **all 262,144
C1 leaf positions**. The existing theorem gives `|S| ≤ 262144`. No later
opening position can enlarge this prefix-fixed set.

The new model allows an adaptive continuation to choose raw hash inputs after
seeing all previous **256-bit** answers. It maintains a lazy-oracle cache:
known inputs return the old answer; fresh inputs consume one of at most `Q`
fresh answers. The continuation has at most `steps` call opportunities and
may halt early. A fresh request after budget exhaustion returns an explicit
aborted result; it supplies no answer and is not inserted in the answered-call
log. Repeated calls may continue after the fresh budget is exhausted.

The theorem constructs the target-counting tree from that machine. It proves,
rather than assumes, that a target-valued answer at an input absent from the
original cache entails a fresh charged target hit. Old cache entries remain
unchanged, and every recorded answer is present in the final cache.

For the C1 instantiation, `WholeDomainLaterHit` is evaluated on the machine's
actual final log and its final cache projected to the first 26 bytes. A logged
input absent from the initial prefix has a returned full answer; its projected
target membership therefore implies full-answer membership in the lifted
target set. The default used to totalize an unqueried input cannot create this
event, because the input must occur in the answered-call log.

V7's exact projection theorem gives

```
|prefix208^-1(S)| = |S| * 2^48 ≤ 262144 * 2^48.
```

Keeping the unused 48 bits in the continuation's observation is important:
this is not a proof for a restricted adversary that sees only 208-bit answers.

The kernel-checked endpoint is the following probability bound under the
literal uniform full-answer tape:

```
Pr[WholeDomainLaterHit in gameRun]
  ≤ Q * (262144 * 2^48) * (2^256)^(steps-1) / (2^256)^steps.
```

For `steps > 0`, ordinary exponent cancellation rewrites that displayed
quantity as `Q * 262144 / 2^208 = Q / 2^190`. The Lean endpoint retains the
exact-count expression above, including its harmless zero-step convention;
the simplified display is not a separate numerical security certificate.
There are no positive work/grinding bits, prescribed adversary query budget,
or claim about unlimited offline search.

This replaces the previous *unbounded* whole-domain-later-hit model event
with a concrete causal resource bound. It does **not** establish that all
accepted V8 executions have sufficient authenticated C1 support or a valid
payment witness. The raw-log collision alternative remains separate and
shared; this result does not pay it once per leaf or add an extra q22 union.

## Exact interfaces and proof reuse

| Interface | Newly established or reused | Status |
|---|---|---|
| `run_preserves_cache`, `run_calls_cached` | Old answers persist; answered calls cannot disagree with final cache | New, kernel checked |
| `run_target_entry_from_old_or_hit` | Relative to a fixed original cache, target-valued new entries require a constructed fresh-hit event | New, kernel checked |
| `new_target_event_count_le` | Exact count of bad tapes bounded by `Q * targetCap * |Output|^(steps-1)` | New machine-to-tree reduction; reuses `V7BudgetedAdaptiveTargets.budgeted_causal_hit_count_le` |
| `fullTargets_card_le` | Actual runtime SHA-256 first-26-byte target preimage has cap `262144 * 2^48` | Existing whole-domain C1 target cardinality plus V7 exact prefix projection |
| `game_event_implies_new_target_event` | `WholeDomainLaterHit` for the defined final log/view implies the cache machine event | New, kernel checked; no supplied source-event-inclusion premise |
| `game_count_le`, `game_probability_le_exact_count` | Concrete 256-bit counting and uniform-PMF endpoint | New, kernel checked |
| Source hash log and root-prefix timing → this `Strategy`/cache/tape | Complete actual call capture, identical cache semantics and conditional fresh-answer law | **Unresolved source/experiment coupling** |
| Authenticated support → optional early C1 identification | Previous per-opening/large-support bridge, preserving late-hit and collision alternatives | Reused, not replayed; support availability still required |

`Strategy` is a bounded mathematical decision tree, not an efficient compiled
extractor. Each continuation depends only on already returned answers. Private
coins can be fixed when selecting a strategy; averaging over independent coins
or a random early prefix is a further coupling/averaging step, not a source
theorem supplied here. The target theorem is pointwise in every fixed prefix,
root, and strategy under the explicitly fresh uniform continuation law.

The tape has one coordinate per potential call, including cached/free calls.
The machine ignores the coordinate at a cache hit. Such dummy coordinates
cancel in the counting argument; “free” means **no fresh oracle answer**, not
zero runtime, hash-system cost, or verifier CU.

## What is still not supplied by a root or by this game

1. The early prefix contains full input/answer records available in the
   experiment, not data reconstructible from a root alone. The source coupling
   must establish their provenance and freeze them before the relevant early
   challenges. For the existing authentication theorem, all recorded answers
   must agree with the actual oracle; an arbitrary inconsistent record list
   is not silently declared an actual hash transcript.
2. This machine has a monotonically extending oracle cache. It does not model
   erasing the cache on rewind, resampling a previously queried input, oracle
   programming, or restarting at a favourable prefix without charging that
   selection. Actual forks/restorations and retries need their own schedule
   coupling and total fresh-query budget. Absorbs, malformed proofs, verifier
   hash calls and extractor calls cannot be omitted from the relevant source
   log merely because they are not Merkle openings.
3. Fresh-budget exhaustion is visible in the returned result, but no theorem
   here says an extractor succeeds before exhaustion. Accepted replay/fuel/
   missing-response failures remain in the actual `A AND NOT X` event. The
   `steps` index bounds call depth; a zero-step `halt` returns `aborted=false`
   and is not a model of all provider-fuel/replay abort classes.
4. A q22 proof does not expose 245,609 authenticated fibres. Previous
   large-support identification still needs legitimate access/rewinds or a
   proved alternate recovery route. Mathematical totalization of a partial
   word does not by itself provide canonical leaf evidence on that support.
5. The `fullTargets` finite set is a mathematical construction over a huge
   finite type; it is used symbolically, not enumerated or proposed as an
   executable algorithm. This is not an extractor runtime measurement.

The next decisive authentication experiment is to couple the instrumented
full-answer recorder and each actual hash call/replay boundary to this cache
machine, with one explicit total `Q`. The recorder controls produced in the
parent task are differential evidence; they are not promoted here into that
universal source coupling.

## Pins, execution and evidence

Research dependency pin:
`bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`.
Research HEAD at game checks:
`4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e` (new work preserved).
Borrowed V7 source/olean closure pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The first preflight correctly refused a mismatched `V7Tag73ResourceLazyOracle`
source/cache pair. The explicitly reviewed newer V7 closure is used instead:
its changed literal transcript-count constants are **not** used in these
generic theorems. Every reachable Aspis import is checked against that
immutable V7 pin, with source and cached-olean SHA-256 recorded before and
after the successful dependent run. Previously proved research import
sources are checked against the research pin. The final runner follows
imports from the exact borrowed source closure, not from an older worktree.

Lean 4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
Only focused cached leaves were compiled. The runner sets Lean `-M7000` and
guards aggregate job-descendant RSS at 7 GiB. No other local heavy job ran in
the assigned slot; no cold build, SBF build, remote job or unchanged theorem
replay was started.

| Target/log | Exit | Wall seconds | Peak RSS bytes | Swaps | Outcome |
|---|---:|---:|---:|---:|---|
| `early-c1-oracle-machine-v1.log` | 2 | n/a | n/a | n/a | Provenance refusal before Lean |
| `early-c1-oracle-machine-v2.log` | 1 | 20.76 | 5511315456 | 0 | Local dependent-recursion/interface errors |
| `early-c1-oracle-machine-v3.log` | 1 | 22.58 | 5503713280 | 0 | Local query-equation/cache-proof errors |
| `early-c1-oracle-machine-v4.log` | 0 | 17.92 | 5664702464 | 0 | Generic machine/count endpoint passed |
| `early-c1-oracle-game-v1.log` | 1 | 24.69 | 5604605952 | 0 | Map eta reduction and unnamed-section close |
| `early-c1-oracle-game-v2.log` | 0 | 9.52 | 5750390784 | 0 | C1 model-event and probability endpoint passed |

Failures are retained; none was retried unchanged after a memory kill.
The successful axiom audits contain only `propext`, `Classical.choice`,
and/or `Quot.sound`, with no `sorryAx` or new axioms. Failed logs contain Lean's
error-propagation `sorryAx`; those are not claimed results.

Final new source / olean SHA-256:

| Leaf | Source | Olean |
|---|---|---|
| `EarlyC1OracleMachine` | `8d580172056facaf62e2bd4485c18545ef5a154571469aa25d7a81cf8d8f477a` | `3d5fba15c20aff6510397e7bbeb7a71ca86e7f0922652699a10d3e6412ed2e4e` |
| `EarlyC1OracleGame` | `e1f7db8a51343924b3994b807ffa62d27bd63567e88ee0ba564faf3006b67be1` | `98c6d9bd2d9c56a1d5e983122914b171f2faadad47d90757690551dc9abbe7c0` |

Reproduction from the research worktree (use fresh log paths; existing logs
are deliberately not overwritten):

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_oracle.sh \
  /tmp/early-c1-oracle-machine-replay.log EarlyC1OracleMachine
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_oracle.sh \
  /tmp/early-c1-oracle-game-replay.log EarlyC1OracleGame
```

Do not repeat these unchanged checks merely because another research file
changes. Compiled oleans stay in the ignored local cache; committed sources,
runner and logs preserve the result and provenance.

No production or verifier code changes occur in this subtask. QM31/q22,
the domain and the canonical proof-body census remain unchanged:
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
No new CU, prover-time, memory-of-proving, hiding, payment-recovery or global
Fiat–Shamir/security claim follows from these Lean measurements.
