# Runjoin55 — conditional native publication extended; six links retained

Entry **fc300a706a9830e56d6e93e1bfeff31b10c973ba**, worktree
`/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`. Commits are listed in `commits.txt`.

**Target not yet established. No whole ledger row or endpoint premise was
removed.** All six requested publication links remain open. Their definitions
are byte-identical to entry; no conclusion was substituted for a producer law.
Step (4) has not started. Protected prefixes and frozen Rust/client sources
remain unchanged.

## Checked conditional composition

`PV_RunJoin_NativePublication55.complete` passed at **67788**. Its conclusion
is the unchanged `PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT`, now over the
full `prover.prove_masked_with_attempt` input family, rather than only the
`prove_from_semantics` slice.

`PV_RunJoin_NativeAttemptPublication55.complete` passed at **67792**. It
extends that same typed conclusion through the original
`prover.prove_masked_attempt`, including its actual public-byte computation,
context creation, mask nonce, variant tag, binding hash and durable nonce store.
`NativeControlSource55.complete` (67783) and `NativeAttemptLaws55.source`
(67791) identify the factored callers with the original source functions.
The relational composition preserves complete Results, errors, divergence,
audit values and nonce-store state. It does not assume caller success.

Both theorems retain exactly the six fixed publication links, instantiated
on `NativeCallback55.runOf data plans`. `data` and `plans` remain families over
native phase inputs. Their satisfaction by the reachable native producer is
**not established**. No backend-message equality, canonical producer input,
stored weight object or complete publication equation is promoted to an
installed native fact.

The model callback preserves actual failure/error outcomes and tests source
success, then constructs successful proof bytes from the independent ordered
assembly. Its successful-byte construction does not consume the actual proof
bytes. The S2 restriction is derived at each native phase constructor, not
postulated as a fact about arbitrary dictionaries. The attempted generic
`SourceSuccessVariant55` is rejected and uncredited: op233 is caller-supplied
there, so its variant test cannot be reduced by `rfl`.

`PV_RunJoin_NativeToRP55.complete` passed at **67795**. It specializes the full
native-attempt conditional byte equation to the hash function of the original
`toRP W Pr R h B outputs x w hN s` table. **This is a hash specialization,
not the complete original common-sample association.** It does not establish
native public/witness association, stored records, the coefficient trace, the
coupling, or either observable decoder. The original address/causality and
collision/public-address conditions remain explicit in the separate checked
common-circle source theorems; this specialization does not discharge them.

## Fixed link status

| Link | Status and exact progress |
| --- | --- |
| CommonSample | **Open.** Repaired the recorded map carrier mismatch at 67700. Both total fallback outputs, canonical circle coordinates and security-model coordinates are now checked. `CommonCircleFirst55.complete` (67727) and `CommonCircleSecond55.complete` (67734) associate both original framed transcript calls with the original common tape, retaining RAddrIn, RCausal, collision/public-address guards, parser errors and both Result layers. Complete semantic/opening challenge threading, returned/stored records, all Data fields and coefficient-trace composition remain. |
| BackendInput | **Open.** Checked exact mutation-restoration binding and symbolic preservation of message length 29 through every C1/C2 row/column loop and both commitment producers (`BackendC1Length55`, 67748; `BackendC2Length55`, 67749). Actual native initialization, the complete build_with_material state invariant, pointwise hinput/message association and canonical coefficient derivation remain. The broad build aggregation is rejected, not a producer premise. |
| FinishContext | **Open.** Actual folded leaves/tree/root, tag 30, final fold, tags 31/32, public checks and front-field association remain. No discharge this round. |
| QueryAppend | **Open.** Actual 22 source appends and ordered six parts per query remain. No discharge this round. |
| NodeAppend | **Open.** Six multiproofs, sorted/deduplicated indices, padding and complete byte/error association remain. No discharge this round. |
| PublishOrder | **Open.** Concrete serializer constants, guards, compact semantic/claim fields, openings and query/node ordering remain. The extended conditional theorem consumes this link; it does not prove it. |

R24Sampler remains discharged by the unchanged runjoin54 theorem.

**Rows removed: none.** In particular V038, V045, V163, V165, V167, V244,
V258–V260 and V262 receive no whole-row credit. Endpoint P changes:
removed/added/weakened/changed **0/0/0/0**. The same eight endpoint fields and
three TrustItems are retained. V370, D381/D386, op79/op254 and the deployed
disclosed/observerOracle installations remain explicit. Observer, simulator,
coupling, bad/query events, failure independence and side-channel scope are
unchanged. Original privacy is not established.

## Verification, failures and resource discipline

**100 Lean attempts exhausted, IDs 67700–67799; zero Kani.** There are
61 successful compiler exits and 39 rejected attempts. Attempt **67723 is
excluded from credit** for the sequencing violation below. Thus 60 accepted
attempts are credited: 57 non-audit modules and three audits.

All scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and
Lean -M7000. Maximum recorded RSS was **7,442,853,888 bytes**; every swap count
was zero. 67719 and 67722 hit kernel memory checks. Their replacements split
literal-row dispatch, selector, byte-state and dictionary equations; no limit
was raised. Native caller heartbeat failures were replaced by named stages
and explicit bind/branch congruence, not by raised limits.

**Recorded sequencing error:** 67723 overlapped the tail of 67722. It is
uncredited and no credited consumer imports its module. The restoration law
was independently compiled as `BackendStoreSafe55` at 67728. The wrapper now
refuses to launch while an own scope is running, and later compiles were
collected sequentially. Atomic admission checks were compliant for all 100
launches; that admission audit is separate from this scope-overlap finding.

The line-wide failed-source guard checks prior runjoin failure hashes before
every launch. Its final SHA-256 is
`7b389e207b7ac17d087ae29bd0b5a89f180893d6276b5aac7d7cd41edaae7b0a`.
No unchanged failed source was resubmitted this round. Every rejected source
is retained by its verified Git blob in `retained-failed-sources.json`.

Final audit source revision: **639889dc0c3239cf656ddaff431604271202651d**.
All added credited theorems are covered by the three audits. The 110 named
prints and imported closure are recorded in `audit-design.json` and
`audit-coverage.json`; `NativeAfterAudit55.run` is an imported definition with
its own accepted axiom print at 67767. Every credited printed axiom set is a
subset of propext, Classical.choice and Quot.sound.

| ID | Exact target | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 67797 | R1Z.PV_RunJoin_CircleAudit55 | 0 | 1.75 | 4469932032 | 0 |
| 67798 | R1Z.PV_RunJoin_BackendAudit55 | 0 | 1.65 | 4404232192 | 0 |
| 67799 | R1Z.PV_RunJoin_NativeAudit55 | 0 | 1.67 | 4480618496 | 0 |

Every receipt records target, exit, scope wall, peak RSS, swap, source revision,
source/object hashes, dependency fingerprint and original axiom lines. All
200 original module output/time files were hash-verified and retained in
`original-module-logs.json.xz`. Rejected/sorryAx outputs earn no credit.

The final read-only cache preflight matched **3,575** project source/object
pairs, **7,903** direct dependency fingerprints, **5,673** external objects
and **5,438** IR companions, with the identical pinned toolchain and LEAN_PATH.
The cache includes the explicitly uncredited 67723 artifact for provenance;
it is excluded from the credited audit roots and consumers. The private
workspace and caches are retained; no shared or other-job objects were
modified. Final own running scopes: zero.

The final focused failure, 67796 `CommonCircleSuccessFirst55.complete`, is
uncredited: a `dsimp only at heq` makes no progress. Its dependency theorems
and generic Result-success helper are accepted. The second returned-record
composition is retained only as `.lean.txt` under `uncompiled-drafts/`; it
was never submitted. `BackendBuildLength55` and the generic variant attempt
remain explicitly rejected as well.

No full frozen release manifest, Kani, Rust build, native differential,
extraction, ELF operation or step-(4) installation ran. Frozen Rust/client
source still equals 82566acdfb under the relevant paths. No key was accessed,
destroyed or cleaned up. Work stops on the exhausted Lean budget.
