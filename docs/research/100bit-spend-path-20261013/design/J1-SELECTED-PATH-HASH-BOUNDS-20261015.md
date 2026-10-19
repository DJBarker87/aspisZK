# Selected guarded Pool-path query and hash-call inventory

Inspection base: `e4a5808dd061cf373b27d130f7d66eb8f0214db9` (worktree HEAD). This is a source and existing-theorem inventory for the selected `pool-adapter` build. It separates (1) abstract first-read budgets, (2) source-visible `HashFn` calls, and (3) Solana PDA/CPI work. It does not assign a security budget, prove a source refinement, or close a global all-input query bound.

## Reachable guarded inputs

With `pool-adapter`, `programs/r1-cost-probe/src/lib.rs:31–37` forwards instructions whose first byte is 4, 5, or 6; exact `[3,10]` or `[3,11]`; or prefix `ASQ8`. `r1_pool_adapter.rs:982–993` routes 4/5/6 to lifecycle init/write/finalize, the two exact stage-1 tags to `stage1`, and the remaining admitted input to `stage2`. Stage 1 itself rejects any other byte sequence and requires two accounts (`:868–884`). Stage 2 requires six accounts and ASQ8 magic (`:940–948`). The old `[1,k]`/`[2]` route in `lib.rs:39–61` is under `cfg(not(feature="pool-adapter"))`; it does not participate in this selected feature build.

The lifecycle handlers check instruction/account layout, authority and bounded body copy/clear, but have no `HashFn`, `find_program_address`, or CPI call on their route (`r1_pool_adapter.rs:277–361`, also summarized in `J1-ORACLE-CALL-INVENTORY-20261015.md`). Thus `[4]`, `[5]`, `[6]` contribute no R1 verifier callback calls or verifier query loop. This statement is limited to the audited adapter lifecycle handlers; it is not a claim about unrelated Pool instructions.

## S2 verifier query and raw callback counts

The successful selected ASQ8 path fixes `Variant::S2`. The adapter stage-one `data[1]` supplies `k=10` or `11` to `verifier::tx1` (`r1_pool_adapter.rs:929`; `lib.rs:24–27`). `tx1` rejects `k>22`, fully parses proof shape/field encodings, verifies the semantic prefix, prepares challenges and all 22 query indices, then runs `while a.next < k` (`verifier.rs:342–349`). Stage 2 validates ASQ8 and checkpoint framing, encodes the exact public statement, then calls `tx2_authenticated`; that routine resumes the checkpoint and runs `while a.next < 22` (`r1_pool_adapter.rs:948–977`; `verifier.rs:380–385`). The q22 transcript computes eight squeeze/advance pairs once at row 31 (`transcript.rs:35–45`); those are not regenerated per selected query.

For one fully successful S2 execution, source-visible callback accounting is:

| Work | Stage 1 `[3,k]` | Stage 2 | Basis |
|---|---:|---:|---|
| Semantic rows + opening transcript/challenge preparation | 115 | 0 | `r1_semantic::verify_observed` rows 0–26 and `Prepared::new`; prior inventory gives 82 semantic calls + 33 later transcript calls |
| q22 generation | included in 115 | 0 | 1 absorb + 16 precomputed block calls |
| Query Merkle verification | at most `21k` | at most `21(22-k)` | S2 has two private leaf hashes + twelve path-parent hashes and one folded leaf + six parents per processed index |
| Checkpoint write/read | 3 | 3 | hash proof, public bytes and checkpoint checksum/prefix in each phase |
| Successful-stage expression | `118 + 21k` | `3 + 21(22-k)` | Adds to 583 when both phases finish |

Consequently the source-count totals for the two allowed splits are:

| Stage-one tag | Stage 1 max | Stage 2 max | Two-phase total |
|---|---:|---:|---:|
| `[3,10]` | 328 | 255 | 583 |
| `[3,11]` | 349 | 234 | 583 |

These are raw calls through the supplied `HashFn` on the complete successful S2 path. They are not distinct input counts. On rejecting paths the verifier may stop early: both C1/C2 leaf digests are formed before path tests, the C2 path is short-circuited if C1 fails, and the folded leaf/path is reached only if both initial paths pass (`verifier.rs:242–263`). A path itself executes six parent hashes before comparing its final root (`:120–128`). The 583 count was independently observed by the P3 counter on one saved pair; that run measured 452 union-distinct input byte strings (297 in tx1, 179 in tx2, 24 shared), not a universal upper bound (`evidence/hash-input-counter-p3-20261014/README.md`).

The fixed-shape S2 proof length is 124,343 bytes; the adapter-produced public statement is 1,880 bytes. The existing [`J1-HASH-INPUT-LENGTH-INVENTORY-20261015.md`](J1-HASH-INPUT-LENGTH-INVENTORY-20261015.md) lists each concatenated input width and notes that lower-level verifier APIs accept arbitrary public-byte slices. The 124,343/1,880 maxima therefore depend on the selected adapters' strict framing and checks, not the lower-level function types in isolation. Stage 2 invokes the authenticated entrypoint, whose comment requires an authentic stage-one checkpoint for the same immutable proof/public data; it does not repeat strict field-canonical scanning (`verifier.rs:368–385`).

## PDA derivations and CPI, separate from callback hashes

Stage 1 and lifecycle 4/5/6 do not authenticate ASQ8 PDAs and do not call the Pool terminal/CPI route. ASQ8 stage 2 reaches `validate_asq8` (`r1_pool_adapter.rs:808–841`), which authenticates six accounts, reconstructs the statement and scans the proof account before the verifier continuation. Adapter authentication has three direct `Pubkey::find_program_address` sites for master, checkpoint, and lane (`:615–667`). It additionally authenticates a v1 registry/entry with two direct derivations or, on the immutable-deployment branch, v2 registry, registry ProgramData, entry, and verifier ProgramData with four (`:477–581`). Thus that adapter branch has five or seven direct derivation call sites on successful authentication. The SDK's internal bump-search SHA work is not exposed as a fixed count by these call sites.

The Pool `ASQ8` terminal path has separate PDA and CPI work. The existing call-site map in [`J1-ORACLE-CALL-INVENTORY-20261015.md`](J1-ORACLE-CALL-INVENTORY-20261015.md) identifies Pool master/checkpoint/lane validation, one or two root-history page derivations depending on fresh/rollover state, verifier registry v1/v2 branches, and nullifier marker derivation with a possible post-creation recheck. The Pool makes one verifier CPI; marker setup can make zero, one, or two/three System CPIs depending on marker ownership/funding, and withdrawal adds one token CPI (`pair_forest_dispatch.rs:220–279`, `processor.rs:300–372,1505–1545`, `pair_forest.rs:1532–1542`). These are not calls to the verifier's `HashFn`. The Pool terminal code has no direct `HashFn` callback call; prepared-settlement APIs are another route and excluded from this ASQ8 path.

The direct-PDA call-site inventory is not a bound on SDK-internal SHA attempts, and branch-dependent Pool derivations/CPI are not collapsed into one number here. In particular, the ASQ8 request's own fixed framing and lifecycle operations do not remove the account/state-dependent branches in terminal authentication and settlement.

## Reusable formal bounds, and the remaining bridge

The existing formal query bound is [`UnifiedQueryDensity.queryCap`](../lean/UnifiedQueryDensity.lean), defined as `choose 9557 22 / choose 262144 22`. `query_density_bound` gives a conditional row-31 selected-query density bound; `query_first_hit_bound` scales it by a supplied `FirstReadsBound q t N`. The literal adapter theorem [`LiteralQueryDensity.row31_density`](../lean/LiteralQueryDensity.lean) derives the selected set from its literal prefix and message. [`LiteralQueryReadFacts.chalSet_card_eq_22`](../lean/LiteralQueryReadFacts.lean) supplies the deterministic cardinality fact for a successfully decoded list. [`LiteralRhoDensity.row32_density`](../lean/LiteralRhoDensity.lean) is a separate row-32 rho residual density bound. These are event-density theorems, not a source-level count of all reads/hash calls on the Pool path.

For the 33-row adaptive fresh-answer interpreter, `FreshAttemptBound.thirty_three_hitMass_lt` requires a per-row density premise and proves a fresh-row union bound; [`UnifiedFreshAttempt.thirty_three_rows_lt`](../lean/UnifiedFreshAttempt.lean) instantiates it with the abstract `UnifiedEventDensity.density_bound` and explicit sampler identities. The literal sampler has `LiteralByteSampler.eval_eq` and `independentMean_eq`, and `LiteralByteProtocol.d1`/`d2` are parameterized by a supplied decoder. These results do not by themselves turn the memoized source `HashFn` trace into independent answers or show the required first-read injection for all source paths.

At the all-input level, `UnifiedOracleTotalCase` and `UnifiedOracleInj.inj` take a `firstReads ... ≤ Qtot`/distinct-first-read budget as a premise. The existing `UnifiedOracleTrace` decomposes the source-model verifier trace; it is still an abstract program trace theorem. No theorem found in this pass derives the required universal `Qtot` bound from every reachable Pool ASQ8 account/authentication branch, SDK PDA bump search, CPI and source verifier execution. `J1-ORACLE-CALL-INVENTORY-20261015.md` and `J1-HASH-INPUT-LENGTH-INVENTORY-20261015.md` remain the exact source call/width inventories; this note does not replace them with a QV conclusion.

## Source pins

The following current source hashes were checked at the inspection base above:

| Source | SHA-256 |
|---|---|
| `programs/r1-cost-probe/src/lib.rs` | `36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-core/src/r0/merkle.rs` | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| `programs/aspis-pool/src/pair_forest.rs` | `d96b352bae081a72d6e887759a356674598e0bf3a177c8d103885f02bc344c30` |
| `programs/aspis-pool/src/pair_forest_dispatch.rs` | `7e45910a3d64e328dc234ede290119770e898bcb48f277d978219740ec891514` |
| `programs/aspis-pool/src/processor.rs` | `3c989ba201b622c01e67edec7cba8b17ba30663b386a4f316e757ff06dad7354` |
| `programs/aspis-pool/src/history.rs` | `7d754900fecb4d6ba4511029a3617e90f91c697fc415fabd8aa4b2c0c519107a` |
| `programs/aspis-pool/src/registry.rs` | `99c166a1f6641631937450fe7e59e08cb6422e588d8c49b90f66f9a4cb85ed8a` |
| `programs/aspis-pool/src/nullifier.rs` | `274398d59536f19fa25dd11269945893fe02a03e5668655244b7be2f32e26c6f` |
