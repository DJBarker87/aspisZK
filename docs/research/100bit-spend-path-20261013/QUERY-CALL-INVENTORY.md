# Rust hash-call inventory (source-only)

Inspection base: `a9d4c4bee5e2cf34ac91056b9e9a7a7ab4e1643f`. This note counts source-visible calls to the supplied `HashFn` in the R1 cost-probe paths. It separates raw hash invocations from distinct hash inputs. No build or runtime measurement was performed for this inventory.

## Transcript sampler and row schedule

`r1_wire::SemanticTranscript::new` performs one initial hash over the public bytes and C1 root (`crates/aspis-r1-cost-probe/src/r1_wire.rs:173-180`). Each `sample_block_validated` performs three calls: the row absorb, squeeze from the absorbed state, and advance from that same absorbed state (`r1_wire.rs:189-202`). The successful semantic path samples rows 0 through 26: 27 rows × 3 calls, plus initialization, or **82 raw calls**. The caller flow is in `crates/aspis-r1-cost-probe/src/r1_semantic.rs:70-77, 83-100, 127-130` and `r1_wire.rs:342-350`.

The later transcript constructor hashes its domain, variant tag, and semantic state once. A scalar block uses an absorb, squeeze, and advance (3 calls); q22 uses one absorb plus eight precomputed squeeze/advance pairs (17 calls); rho is another scalar block (3 calls). See `crates/aspis-r1-cost-probe/src/transcript.rs:5-45` and call order in `prover.rs:194-229` / `verifier.rs:87-99`. With three scalar rows before q22 for a one-fold variant, the later transcript costs 1 + 9 + 17 + 3 = 30, giving **112 raw transcript calls total**. With the extra row-30 scalar for two-fold variants, it costs 1 + 12 + 17 + 3 = 33, giving **115 raw transcript calls total**.

The q22 sampler requests 22 distinct fibre indices from a range of `2^18`; its scanner permits at most 64 candidate draws, eight 32-byte blocks, and eight words per block (`crates/aspis-core/src/r0_transcript.rs:46-48, 190-224, 249-267, 305-318`). Distinctness here is a property of the selected indices. It is not a measurement or proof that the underlying hash inputs are distinct. The R1 probe materializes all eight squeeze/advance pairs before calling this scanner (`crates/aspis-r1-cost-probe/src/transcript.rs:35-43`).

## Merkle prover and verifier paths

The R0 Merkle tree has `FIBRE_COUNT = 2^18` leaves and six 8-way parent levels (`crates/aspis-core/src/r0/mod.rs:34`; `crates/aspis-core/src/r0/merkle.rs:39-58`). A complete tree therefore performs 262,144 leaf hashes and 36,649 parent hashes (level widths 32,768, 4,096, 512, 64, 8, 1), totaling **298,793 raw calls per tree**. The host commitment builder hashes each leaf once and then constructs this tree (`crates/aspis-r1-cost-probe/src/host_commitment.rs:194-218`). It builds C1 and C2 commitments via `Backend::c1` and `Backend::c2` (`crates/aspis-r1-cost-probe/src/prover.rs:9-19`). Two-fold variants also build a folded tree (`prover.rs:207-223`). Thus the three-tree subtotal is **896,379 raw calls**, before transcript and optional salt derivation.

The verifier hashes C1 and C2 leaves and checks two six-level paths for each query; two-fold variants also hash the folded leaf and check its six-level path (`crates/aspis-r1-cost-probe/src/verifier.rs:120-128, 242-263`). That is 2 leaf calls + 12 parent calls = 14 per query for one-fold, or 3 leaf calls + 18 parent calls = 21 per query for two-fold. Across the 22 queries, these are **308** and **462 raw verifier calls**, respectively. Each path level consumes seven sibling digests but invokes one 8-way parent hash (`r0/merkle.rs:77-103`). The indices are without replacement, but path hash inputs are not deduplicated or instrumented.

With the cost-probe checkpoint protocol, `checkpoint` hashes proof, public bytes, and checkpoint body, while `resume` rehashes those three inputs (`crates/aspis-r1-cost-probe/src/verifier.rs:302-316, 325-328`). That adds six raw calls across a successful tx1+tx2 verification, with three exact input byte strings repeated across phases. The visible successful verifier subtotal is therefore **426 raw calls** for one-fold (112 transcript + 308 Merkle + 6 checkpoint) and **583 raw calls** for two-fold (115 + 462 + 6). This count covers the source-visible transcript, Merkle, and checkpoint paths; it does not count distinct random-oracle inputs.

## Private leaf-salt calls and prover subtotal

When `private-leaf-salts` is enabled, each tree leaf still uses one hash (`crates/aspis-core/src/state_only_private_merkle.rs:22-35`). For every salt, `derive_pool_v1_leaf_salt` computes a private attempt binding and then the leaf salt, one hash each (`crates/aspis-prover/src/state_only_entropy.rs:568-585, 854-865`). The R1 probe derives salts separately for C1 and C2 and for the folded tree (`crates/aspis-r1-cost-probe/src/prover.rs:165-169, 182-187, 210-218`). The attempt binding is recomputed per leaf by this call path; it is not cached. Three sets of `2^18` salts therefore add **1,572,864 raw hash calls**. For a two-fold, private-leaf-salts run, the visible transcript + tree + salt subtotal is **2,469,358 raw calls** (115 + 896,379 + 1,572,864).

That is a scoped subtotal, not an upper bound for all honest-prover work. In particular, the masked-attempt setup and mask-material derivation execute additional hash-based expansion paths before `prove_from_semantics` (`prover.rs:131-178`; `state_only_entropy.rs:588-620, 642-674`). I did not count those paths here. The corresponding visible verifier subtotal does not include prover-side salt derivation.

## Instrumentation and recorded artifacts

The R1 `Observer` records phase events, including `Phase::Merkle(i)`, rather than raw hash calls (`crates/aspis-r1-cost-probe/src/verifier.rs:20-24, 264`; `r1_semantic.rs:63-68`). I found no R1 instrumentation that counts distinct oracle inputs or raw hash invocations across the complete prover/verifier run. `crates/aspis-core/src/verify.rs:1530-1543, 1589-1598` has a `HASH_CALLS` counter for a separate OOD-sampling probe; its test checks a 20-call delta and does not cover R1 proof Merkle paths or distinct inputs.

The existing R1 runtime measurement JSON under `docs/research/100bit-spend-path-20261013/evidence/latest/results/100bit-path-20261013/d18-native/S2/measurements/` records verifier transaction measurements, and the summaries record resource/cost results. They do not report hash-call totals or unique oracle-input cardinalities. No measured R1 hash-count artifact was found in this inspection.

## Source hashes

SHA-256 values below are for the cited source files at the inspection base above.

| Source | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/prover.rs` | `a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/host_commitment.rs` | `551c4f8a0df50e0b53ab7e79d4e71b8c6afe417043c55caa1c377da3388f890c` |
| `crates/aspis-r1-cost-probe/src/transport.rs` | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` |
| `crates/aspis-core/src/r0/merkle.rs` | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| `crates/aspis-core/src/r0/mod.rs` | `709f1d0d9be9d3ee74e2b63e13065f5a91c878ba77ed2d2e97a414fbbc646aca` |
| `crates/aspis-core/src/r0_transcript.rs` | `2a315219d20069742c7c07e2a1ab8ee283865be3c607fdde2cf6975ad1813fc1` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| `crates/aspis-prover/src/state_only_entropy.rs` | `78ebbb3176daf23935243452992548ff9d877aaaf853d73e5ee46b60d8cb3ec0` |
| `crates/aspis-core/src/verify.rs` | `108021252ada329b627808c045509eb0678c720b7ed052060213af0763b40656` |

These are mechanical source counts only. They make no security-level or distinct-query-bound claim.
