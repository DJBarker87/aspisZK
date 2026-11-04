# Remaining D members

**Driver root OPEN. 279 functions / 322 D rows remain OPEN.** All 60 Kani, 50 Lean/support and 3 extraction slots are charged (including 3 prelaunch failures). No early-stop or exhausted-Kani waiver is used. The new Lean-only obligations were pursued through L050. No timeout, memory kill, cap raise or unchanged failed prover rerun occurred.

NFQ_REMAINING.json gives every exact callee packet, baseline callee status, domain and certificate shape; NFQ_ORDER.json retains the original bottom-up ordering. The entries below state why each member still requires a native packet. A CLOSED callee alone does not establish its caller.

Priority remains prepare -> Prepared::new / powers / verify_observed -> query_loop -> checkpoint. The Q query_loop boundary remains OPEN pending NFP; independent D leaves are not blocked by that fact. Pool settlement is an external inventory gap owned by NFO. The two uncovered inventory rows remain listed in NFQ_COVERAGE.md.

## crates/aspis-core/src/field.rs::CM31::square

Rows: TX1:011. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::double [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q].

## crates/aspis-core/src/field.rs::CM31::write_le_bytes

Rows: TX2:008. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S].

## crates/aspis-core/src/field.rs::QM31::write_le_bytes

Rows: TX2:024. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::write_le_bytes [D SCC 2]; crates/aspis-core/src/field.rs::QM31::write_le_bytes [D SCC 7].

## crates/aspis-core/src/field.rs::qm31_accumulate_product_channels

Rows: TX1:036. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums

Rows: TX1:037. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field.rs::mul_by_r [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-core/src/field.rs::qm31_m31_dot

Rows: TX1:038. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q].

## crates/aspis-core/src/field.rs::qm31_pack_base4

Rows: TX1:039. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q].

## crates/aspis-core/src/field.rs::qm31_sum_products_small

Rows: TX1:044. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::qm31_accumulate_product_channels [D SCC 8]; crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums [D SCC 9].

## crates/aspis-core/src/field.rs::qm31_sum_products2

Rows: TX1:040. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::qm31_sum_products_small [D SCC 12].

## crates/aspis-core/src/field.rs::qm31_sum_products3

Rows: TX1:041. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::qm31_sum_products_small [D SCC 12].

## crates/aspis-core/src/field.rs::qm31_sum_products3_prepared

Rows: TX1:042. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums [D SCC 9]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-core/src/field.rs::qm31_sum_products4

Rows: TX1:043. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::qm31_sum_products_small [D SCC 12].

## crates/aspis-core/src/field/wide_exact.rs::WideExact::neg

Rows: TX1:054. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::neg [D SCC 19].

## crates/aspis-core/src/field/wide_exact.rs::WideExact::new

Rows: TX1:055, TX2:037. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 [opaque Q].

## crates/aspis-core/src/field/wide_exact.rs::WideExact::square

Rows: TX1:056. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::square [D SCC 21]; crates/aspis-core/src/field/wide_exact.rs::mul_u [opaque Q].

## crates/aspis-core/src/r0/heap.rs::filled

Rows: TX1:064, TX2:045. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest

Rows: TX1:327, TX2:210. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-core/src/r0/merkle.rs::parent_with_digest

Rows: TX1:065. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-core/src/r0_transcript.rs::QueryScan::finish

Rows: TX1:066. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-core/src/r0_transcript.rs::block_rank

Rows: TX1:068. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-core/src/r0_transcript.rs::query_words

Rows: TX1:070. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/r0_transcript.rs::block_rank [D SCC 26].

## crates/aspis-core/src/r0_transcript.rs::QueryScan::scan

Rows: TX1:067. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/r0_transcript.rs::query_words [D SCC 27].

## crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy

Rows: TX1:302. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/poseidon2.rs::external_linear_lazy

Rows: TX1:303. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy [D SCC 29].

## crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy

Rows: TX1:304. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/poseidon2.rs::pow5

Rows: TX1:307. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace

Rows: TX1:306. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/poseidon2.rs::external_linear_lazy [D SCC 30]; crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy [D SCC 31]; crates/aspis-statement/src/poseidon2.rs::pow5 [D SCC 32].

## crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3

Rows: TX1:305. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace [D SCC 33].

## crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent

Rows: TX1:201. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3 [D SCC 34].

## crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots

Rows: TX1:204. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent [D SCC 35].

## crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty

Rows: TX1:203. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots [D SCC 36].

## crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default

Rows: TX1:202. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty [D SCC 37].

## crates/aspis-core/src/r0_transcript.rs::queries_from_pairs

Rows: TX1:069. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/r0_transcript.rs::QueryScan::finish [D SCC 25]; crates/aspis-core/src/r0_transcript.rs::QueryScan::scan [D SCC 28]; crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default [D SCC 38].

## crates/aspis-core/src/state_only_hiding.rs::cm31_mul_i

Rows: TX1:071. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::neg [opaque Q]; crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-core/src/field.rs::QM31::neg [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::neg [D SCC 19].

## crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r

Rows: TX1:072. NFQ_Linear.source proves full canonical model result. K050/K051 direct native value pair is excluded: prescribed field-product opaque-call-log form was not used. Needs an opaque-call-log native packet and paired emitted multiplication law; no Kani multiplication and no rename/retry of this shape.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::double [opaque Q]; crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::double [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-core/src/state_only_hiding.rs::mask_power_26

Rows: TX1:073. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::square [D SCC 1]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::square [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::square [D SCC 21].

## crates/aspis-core/src/state_only_hiding.rs::mul_tower_basis

Rows: TX1:074. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/state_only_hiding.rs::cm31_mul_i [D SCC 40]; crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r [D SCC 41].

## crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears

Rows: TX1:075. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q].

## crates/aspis-core/src/state_only_hiding.rs::state_only_selected_mask_value

Rows: TX1:076. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/state_only_hiding.rs::mask_power_26 [D SCC 42]; crates/aspis-core/src/state_only_hiding.rs::mul_tower_basis [D SCC 43]; crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears [D SCC 44].

## crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points

Rows: TX2:048. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-core/src/state_only_prefix.rs::r0::statement_points

Rows: TX2:047. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points [D SCC 46].

## crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest

Rows: TX1:077, TX2:049. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at

Rows: TX1:078, TX2:050. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys

Rows: TX1:079, TX2:051. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf

Rows: TX1:080, TX2:052. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest [D SCC 48].

## crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index

Rows: TX1:090, TX2:060. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf

Rows: TX1:091, TX2:061. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/compact.rs::slot_offset

Rows: TX1:100, TX2:066. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/candidate.rs::slot

Rows: TX1:092, TX2:062. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/compact.rs::slot_offset [D SCC 54].

## crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys

Rows: TX1:093, TX2:063. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at [D SCC 49].

## crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits

Rows: TX1:118, TX2:084. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels

Rows: TX1:119, TX2:085. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [D SCC 57].

## crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width

Rows: TX1:120, TX2:086. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [D SCC 57].

## crates/aspis-r1-cost-probe/src/multiproof.rs::index_at

Rows: TX1:121, TX2:087. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed

Rows: TX1:128, TX2:094. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/multiproof.rs::node_count

Rows: TX1:122, TX2:088. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [D SCC 57]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels [D SCC 58]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width [D SCC 59]; crates/aspis-r1-cost-probe/src/multiproof.rs::index_at [D SCC 60]; crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed [D SCC 61].

## crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent

Rows: TX1:123, TX2:089. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches

Rows: TX1:124, TX2:090. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent

Rows: TX1:125, TX2:091. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/multiproof.rs::value_at

Rows: TX1:126, TX2:092. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place

Rows: TX1:127, TX2:093. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/r0/merkle.rs::parent_with_digest [D SCC 24]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [D SCC 57]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels [D SCC 58]; crates/aspis-r1-cost-probe/src/multiproof.rs::index_at [D SCC 60]; crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent [D SCC 63]; crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches [D SCC 64]; crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent [D SCC 65]; crates/aspis-r1-cost-probe/src/multiproof.rs::value_at [D SCC 66]; crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed [D SCC 61].

## crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree

Rows: TX1:083, TX2:055. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at [D SCC 49]; crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys [D SCC 50]; crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf [D SCC 51]; crates/aspis-r1-cost-probe/src/candidate.rs::opening [opaque Q]; crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index [D SCC 52]; crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf [D SCC 53]; crates/aspis-r1-cost-probe/src/candidate.rs::slot [D SCC 55]; crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys [D SCC 56]; crates/aspis-r1-cost-probe/src/multiproof.rs::node_count [D SCC 62]; crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place [D SCC 67].

## crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values

Rows: TX1:082, TX2:054. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree [D SCC 68].

## crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle

Rows: TX1:081, TX2:053. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values [D SCC 69].

## crates/aspis-r1-cost-probe/src/compact.rs::check_values

Rows: TX1:096. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::QM31::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::echeck

Rows: TX1:189. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan

Rows: TX1:084. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::M31::from_le_bytes [opaque Q,S]; crates/aspis-core/src/field.rs::QM31::from_le_bytes [opaque Q]; crates/aspis-r1-cost-probe/src/candidate.rs::opening [opaque Q]; crates/aspis-r1-cost-probe/src/compact.rs::check_values [D SCC 71]; crates/aspis-r1-cost-probe/src/verifier.rs::echeck [D SCC 72].

## crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape

Rows: TX1:086, TX2:057. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S].

## crates/aspis-r1-cost-probe/src/candidate.rs::wide_view

Rows: TX1:095. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/compact.rs::expand_values

Rows: TX1:099. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic

Rows: TX1:098. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/compact.rs::expand_values [D SCC 77].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark

Rows: TX1:130. Needs deployed None-observer erase/rename-stability certificate (ae), exact emitted trace equality and matched native controls. General Option<fn> shapes stay quarantined.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new

Rows: TX1:143. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields

Rows: TX1:252. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::frontier

Rows: TX1:253. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields [D SCC 82].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public

Rows: TX1:249. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public

Rows: TX1:266. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic

Rows: TX1:255. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public [D SCC 84]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public [D SCC 85].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes

Rows: TX1:254. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields [D SCC 82]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::frontier [D SCC 83]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic [D SCC 86].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::public_transcript

Rows: TX1:131. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new [D SCC 81]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes [D SCC 87].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record

Rows: TX1:140. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record

Rows: TX1:141. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record [D SCC 89].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k

Rows: TX1:147. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::QM31::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::claims

Rows: TX1:129. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record [D SCC 90]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k [D SCC 91].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary

Rows: TX1:132. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::QM31::add [opaque Q].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value

Rows: TX1:135. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated

Rows: TX1:144. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed

Rows: TX1:148. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row

Rows: TX1:149. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass

Rows: TX1:162. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/sampler.rs::qm31_digits

Rows: TX1:161. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass [D SCC 98].

## crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample

Rows: TX1:163. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-r1-cost-probe/src/sampler.rs::qm31_digits [D SCC 99].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated

Rows: TX1:145. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated [D SCC 95]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed [D SCC 96]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row [D SCC 97]; crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample [D SCC 100].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round

Rows: TX1:133. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary [D SCC 93]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value [D SCC 94]; crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record [D SCC 90]; crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated [D SCC 101]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k [D SCC 91].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds

Rows: TX1:134. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round [D SCC 102]; crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record [D SCC 90]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k [D SCC 91].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload

Rows: TX1:139. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record [D SCC 89].

## crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample

Rows: TX1:156. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample [D SCC 100].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::circle_validated

Rows: TX1:142. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated [D SCC 95]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed [D SCC 96]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row [D SCC 97]; crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample [D SCC 105].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state

Rows: TX1:146. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand

Rows: TX1:212. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::at_point

Rows: TX1:210. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand [D SCC 108].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::boxed_at_point

Rows: TX1:211. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::at_point [D SCC 109].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis

Rows: TX1:209. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active

Rows: TX1:208. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis [D SCC 111].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight

Rows: TX1:226. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis

Rows: TX1:214. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight [D SCC 113].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual

Rows: TX1:215. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot

Rows: TX1:216. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_value

Rows: TX1:217. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot [D SCC 116].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values

Rows: TX1:219. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::qm31_sum_products_up_to4

Rows: TX1:225. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::qm31_sum_products2 [D SCC 13]; crates/aspis-core/src/field.rs::qm31_sum_products3 [D SCC 14]; crates/aspis-core/src/field.rs::qm31_sum_products4 [D SCC 16]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis

Rows: TX1:220. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_value [D SCC 117]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values [D SCC 118]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::qm31_sum_products_up_to4 [D SCC 119].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight

Rows: TX1:222. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31

Rows: TX1:221. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values_windowed

Rows: TX1:224. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31 [D SCC 122].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values

Rows: TX1:223. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values_windowed [D SCC 123].

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors

Rows: TX1:218. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active [D SCC 112]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis [D SCC 114]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual [D SCC 115]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis [D SCC 120]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight [D SCC 121]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values [D SCC 124].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high

Rows: TX1:262. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::poseidon_selectors

Rows: TX1:248. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high [D SCC 127].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim

Rows: TX1:259. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row

Rows: TX1:213. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted

Rows: TX1:230. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31

Rows: TX1:243. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored

Rows: TX1:244. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 [D SCC 132].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes

Rows: TX1:228. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row [D SCC 130]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted [D SCC 131]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored [D SCC 133].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored

Rows: TX1:247. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes

Rows: TX1:229. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted [D SCC 131]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored [D SCC 136]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high [D SCC 127].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored

Rows: TX1:227. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors

Rows: TX1:241. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption

Rows: TX1:260. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored [D SCC 138]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors [D SCC 139]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high [D SCC 127].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_schedule_lanes

Rows: TX1:232. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted [D SCC 131]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption [D SCC 140].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted_shared_selector

Rows: TX1:231. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10

Rows: TX1:257. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes

Rows: TX1:233. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::CM31::square [D SCC 1]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::QM31::square [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::square [D SCC 21]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row [D SCC 130]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted [D SCC 131]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted_shared_selector [D SCC 142]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10 [D SCC 143].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root

Rows: TX1:239. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_level_packed_selector_tensor

Rows: TX1:234. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root [D SCC 145]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 [D SCC 132].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_levels_packed_selector_tensor

Rows: TX1:235. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_level_packed_selector_tensor [D SCC 146].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry

Rows: TX1:236. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::left_digest_packed_selector_tensor

Rows: TX1:242. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 [D SCC 132].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_carry_packed_selector_tensor

Rows: TX1:245. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 [D SCC 132].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_recipient_packed_selector_tensor

Rows: TX1:246. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 [D SCC 132].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed_selector_tensor

Rows: TX1:251. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_levels_packed_selector_tensor [D SCC 147]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry [D SCC 148]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::left_digest_packed_selector_tensor [D SCC 149]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_carry_packed_selector_tensor [D SCC 150]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_recipient_packed_selector_tensor [D SCC 151].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed

Rows: TX1:250. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed_selector_tensor [D SCC 152].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes

Rows: TX1:258. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed

Rows: TX1:261. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row [D SCC 130]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes [D SCC 135]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes [D SCC 137]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted [D SCC 131]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_schedule_lanes [D SCC 141]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes [D SCC 144]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 [D SCC 132]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed [D SCC 153]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes [D SCC 154].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::validate_transition

Rows: TX1:264. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry [D SCC 148]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root [D SCC 145].

## crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs

Rows: TX1:309. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::new [opaque Q].

## crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy

Rows: TX1:311. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs [D SCC 157].

## crates/aspis-statement/src/state_only_poseidon.rs::pow5

Rows: TX1:326. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::square [D SCC 1]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::square [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::square [D SCC 21].

## crates/aspis-statement/src/state_only_poseidon.rs::full_round

Rows: TX1:315. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy [D SCC 159]; crates/aspis-statement/src/state_only_poseidon.rs::pow5 [D SCC 160].

## crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw

Rows: TX1:314. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed

Rows: TX1:313. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs [D SCC 157]; crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw [D SCC 162].

## crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed

Rows: TX1:312. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed [D SCC 163].

## crates/aspis-statement/src/state_only_poseidon.rs::full_round_packed

Rows: TX1:318. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed [D SCC 164]; crates/aspis-statement/src/state_only_poseidon.rs::pow5 [D SCC 160].

## crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb

Rows: TX1:322. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q].

## crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_columns

Rows: TX1:321. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb [D SCC 166].

## crates/aspis-statement/src/state_only_poseidon.rs::interpolated_full_pair_packed

Rows: TX1:323. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/state_only_poseidon.rs::full_round [D SCC 161]; crates/aspis-statement/src/state_only_poseidon.rs::full_round_packed [D SCC 165]; crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_columns [D SCC 167].

## crates/aspis-statement/src/state_only_poseidon.rs::internal_linear_lazy

Rows: TX1:319. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs [D SCC 157].

## crates/aspis-statement/src/state_only_poseidon.rs::internal_round

Rows: TX1:320. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::internal_linear_lazy [D SCC 169]; crates/aspis-statement/src/state_only_poseidon.rs::pow5 [D SCC 160].

## crates/aspis-statement/src/state_only_poseidon.rs::interpolated_internal_pair

Rows: TX1:324. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::qm31_m31_dot [D SCC 10]; crates/aspis-statement/src/state_only_poseidon.rs::internal_round [D SCC 170].

## crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants

Rows: TX1:316. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy [D SCC 159]; crates/aspis-statement/src/state_only_poseidon.rs::pow5 [D SCC 160].

## crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants_packed

Rows: TX1:317. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed [D SCC 164]; crates/aspis-statement/src/state_only_poseidon.rs::pow5 [D SCC 160].

## crates/aspis-statement/src/state_only_poseidon.rs::leading_pair_packed

Rows: TX1:325. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy [D SCC 159]; crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants [D SCC 172]; crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants_packed [D SCC 173].

## crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected

Rows: TX1:308. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field.rs::qm31_pack_base4 [D SCC 11]; crates/aspis-core/src/field.rs::qm31_sum_products3_prepared [D SCC 15]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-statement/src/state_only_poseidon.rs::interpolated_full_pair_packed [D SCC 168]; crates/aspis-statement/src/state_only_poseidon.rs::interpolated_internal_pair [D SCC 171]; crates/aspis-statement/src/state_only_poseidon.rs::leading_pair_packed [D SCC 174].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts

Rows: TX1:237. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::boxed_at_point [D SCC 110]; crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors [D SCC 125]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::poseidon_selectors [D SCC 128]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim [D SCC 129]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed [D SCC 155]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::validate_transition [D SCC 156]; crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected [D SCC 175].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value

Rows: TX1:240. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::terminal_parts

Rows: TX1:263. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts [D SCC 176]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value [D SCC 177].

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::terminal_qm31

Rows: TX1:256. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic [D SCC 86]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::terminal_parts [D SCC 178].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish

Rows: TX1:136. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/state_only_hiding.rs::state_only_selected_mask_value [D SCC 45]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::claims [D SCC 92]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark [D SCC 80]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds [D SCC 103]; crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload [D SCC 104]; crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record [D SCC 90]; crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::circle_validated [D SCC 106]; crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state [D SCC 107]; crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k [D SCC 91]; crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::terminal_qm31 [D SCC 179].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields

Rows: TX1:154. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record

Rows: TX1:151. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields [D SCC 181].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at

Rows: TX1:152. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record [D SCC 182].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::parse

Rows: TX1:138. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at [D SCC 183].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::begin

Rows: TX1:150. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record [D SCC 90]; crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated [D SCC 101].

## crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed

Rows: TX1:137. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark [D SCC 80]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::public_transcript [D SCC 88]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish [D SCC 180]; crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::parse [D SCC 184]; crates/aspis-r1-cost-probe/src/r1_wire.rs::begin [D SCC 185].

## crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new

Rows: TX1:167. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb

Rows: TX1:165. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries

Rows: TX1:168. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/r0_transcript.rs::queries_from_pairs [D SCC 39]; crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb [D SCC 188]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p

Rows: TX1:155. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/sampler.rs::decode8

Rows: TX1:157. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::new [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::new [D SCC 20].

## crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits

Rows: TX1:159. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample

Rows: TX1:158. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p [D SCC 190]; crates/aspis-r1-cost-probe/src/sampler.rs::decode8 [D SCC 191]; crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits [D SCC 192].

## crates/aspis-r1-cost-probe/src/sampler.rs::ordinary_sample

Rows: TX1:160. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/sampler.rs::decode8 [D SCC 191]; crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits [D SCC 192].

## crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block

Rows: TX1:166. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb [D SCC 188]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar

Rows: TX1:169. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample [D SCC 193]; crates/aspis-r1-cost-probe/src/sampler.rs::ordinary_sample [D SCC 194]; crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block [D SCC 195].

## crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar_k

Rows: TX1:170. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 [opaque Q]; crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample [D SCC 100]; crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block [D SCC 195].

## crates/aspis-r1-cost-probe/src/weights.rs::powers

Rows: TX1:197, TX2:138. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim

Rows: TX1:193. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q]; crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::powers [D SCC 199].

## crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new

Rows: TX1:179. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state [D SCC 107]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new [D SCC 187]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries [D SCC 189]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar [D SCC 196]; crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar_k [D SCC 197]; crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim [D SCC 200]; crates/aspis-r1-cost-probe/src/weights.rs::powers [D SCC 199].

## crates/aspis-r1-cost-probe/src/candidate.rs::prepare

Rows: TX1:087. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/r0/heap.rs::filled [D SCC 22]; crates/aspis-r1-cost-probe/src/candidate.rs::wide_view [D SCC 75]; crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic [D SCC 79]; crates/aspis-r1-cost-probe/src/compact.rs::expand_values [D SCC 77]; crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed [D SCC 186]; crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new [D SCC 201]; crates/aspis-r1-cost-probe/src/verifier.rs::mark [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new

Rows: TX1:174. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/r0/heap.rs::filled [D SCC 22].

## crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value

Rows: TX1:178, TX2:102. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::M31::reduce_u64 [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish

Rows: TX1:175, TX2:099. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value [D SCC 205].

## crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new

Rows: TX1:176, TX2:100. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/r0/heap.rs::filled [D SCC 22].

## crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint

Rows: TX1:186. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/field.rs::CM31::write_le_bytes [D SCC 2]; crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field.rs::QM31::write_le_bytes [D SCC 7]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/candidate.rs::tx1

Rows: TX1:094. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle [D SCC 70]; crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan [D SCC 73]; crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape [D SCC 74]; crates/aspis-r1-cost-probe/src/candidate.rs::prepare [D SCC 202]; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new [D SCC 204]; crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish [D SCC 206]; crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new [D SCC 207]; crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint [D SCC 209]; crates/aspis-r1-cost-probe/src/verifier.rs::mark [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot

Rows: TX2:114. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::polynomial

Rows: TX2:119. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation_round

Rows: TX2:116. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q]; crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::polynomial [D SCC 212]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts

Rows: TX2:127. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/weights.rs::double

Rows: TX2:132. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::Weights::new

Rows: TX2:128. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::sub [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::sub [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::sub [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::sub [opaque Q]; crates/aspis-core/src/state_only_prefix.rs::r0::statement_points [D SCC 47]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts [D SCC 214]; crates/aspis-r1-cost-probe/src/weights.rs::double [D SCC 215].

## crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor

Rows: TX2:130. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::factored_s2_libra_weights

Rows: TX2:133. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::QM31::square [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor [D SCC 217].

## crates/aspis-r1-cost-probe/src/weights.rs::s2_grouped_inactive_pair

Rows: TX2:142. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::grouped_inactive_pair

Rows: TX2:135. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::s2_grouped_inactive_pair [D SCC 219].

## crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor

Rows: TX2:131. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::push_byte_products

Rows: TX2:141. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::process_kind

Rows: TX2:139. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor [D SCC 217]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor [D SCC 221]; crates/aspis-r1-cost-probe/src/weights.rs::push_byte_products [D SCC 222].

## crates/aspis-r1-cost-probe/src/weights.rs::process_regular_kinds

Rows: TX2:140. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/weights.rs::process_kind [D SCC 223].

## crates/aspis-r1-cost-probe/src/weights.rs::high_dot

Rows: TX2:136. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::shared_high

Rows: TX2:143. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor [D SCC 217]; crates/aspis-r1-cost-probe/src/weights.rs::high_dot [D SCC 225].

## crates/aspis-r1-cost-probe/src/weights.rs::partial_dot

Rows: TX2:137. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## crates/aspis-r1-cost-probe/src/weights.rs::shared_partials

Rows: TX2:144. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/weights.rs::partial_dot [D SCC 227].

## crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard

Rows: TX2:145. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair

Rows: TX2:129. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-core/src/field.rs::CM31::add [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul [opaque Q]; crates/aspis-core/src/field.rs::CM31::mul_m31 [opaque Q]; crates/aspis-core/src/field.rs::M31::add [opaque Q]; crates/aspis-core/src/field.rs::M31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::add [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul [opaque Q]; crates/aspis-core/src/field.rs::QM31::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 [opaque Q]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 [opaque Q]; crates/aspis-core/src/r0/heap.rs::filled [D SCC 22]; crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor [D SCC 217]; crates/aspis-r1-cost-probe/src/weights.rs::factored_s2_libra_weights [D SCC 218]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::grouped_inactive_pair [D SCC 220]; crates/aspis-r1-cost-probe/src/weights.rs::powers [D SCC 199]; crates/aspis-r1-cost-probe/src/weights.rs::process_regular_kinds [D SCC 224]; crates/aspis-r1-cost-probe/src/weights.rs::shared_high [D SCC 226]; crates/aspis-r1-cost-probe/src/weights.rs::shared_partials [D SCC 228]; crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard [D SCC 229].

## crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation

Rows: TX2:115. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/trace.rs::value [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot [D SCC 211]; crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation_round [D SCC 213]; crates/aspis-r1-cost-probe/src/verifier.rs::mark [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::new [D SCC 216]; crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair [D SCC 230].

## crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::e

Rows: TX2:105. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k

Rows: TX2:106. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::QM31::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw

Rows: TX2:107. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha

Rows: TX2:121. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k [D SCC 233].

## crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights

Rows: TX2:122. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k [D SCC 233].

## crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries

Rows: TX2:126. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-r1-cost-probe/src/verifier.rs::resume

Rows: TX2:124. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-core/src/r0/heap.rs::filled [D SCC 22]; crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::e [D SCC 232]; crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k [D SCC 233]; crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw [D SCC 234]; crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha [D SCC 235]; crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights [D SCC 236]; crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries [D SCC 237].

## crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common

Rows: TX2:065. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes [opaque Q]; crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle [D SCC 70]; crates/aspis-r1-cost-probe/src/candidate.rs::query_loop [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish [D SCC 206]; crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new [D SCC 207]; crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation [D SCC 231]; crates/aspis-r1-cost-probe/src/verifier.rs::mark [opaque Q]; crates/aspis-r1-cost-probe/src/verifier.rs::resume [D SCC 238]; crates/aspis-r1-cost-probe/src/weights.rs::powers [D SCC 199].

## crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated

Rows: TX2:064. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape [D SCC 74]; crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common [D SCC 239]; crates/aspis-r1-cost-probe/src/verifier.rs::mark [opaque Q].

## crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1

Rows: TX2:149. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1

Rows: TX2:151. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1

Rows: TX2:150. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 [D SCC 242].

## crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1

Rows: TX2:152. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical [opaque S].

## crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master

Rows: TX2:157. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 [D SCC 242].

## crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1

Rows: TX2:153. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1 [D SCC 241]; crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1 [D SCC 243]; crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master [D SCC 245].

## crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public

Rows: TX1:268. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from

Rows: TX2:192. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot

Rows: TX2:193. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot

Rows: TX2:195. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at

Rows: TX2:194. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot [D SCC 249]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot [D SCC 250].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at

Rows: TX2:196. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot [D SCC 249]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot [D SCC 250].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable

Rows: TX2:197. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused

Rows: TX2:198. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable

Rows: TX2:199. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused

Rows: TX2:200. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero

Rows: TX2:205. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1

Rows: TX2:206. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot [D SCC 249]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot [D SCC 250]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero [D SCC 257].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1

Rows: TX2:201. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from [D SCC 248]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1 [D SCC 258].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2

Rows: TX2:207. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot [D SCC 249]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot [D SCC 250]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero [D SCC 257].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2

Rows: TX2:202. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from [D SCC 248]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2 [D SCC 260].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1

Rows: TX2:208. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable [D SCC 253]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable [D SCC 255]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero [D SCC 257].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1

Rows: TX2:203. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1 [D SCC 262].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2

Rows: TX2:209. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable [D SCC 253]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable [D SCC 255]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero [D SCC 257].

## crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2

Rows: TX2:204. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2 [D SCC 264].

## programs/r1-cost-probe/src/lib.rs::observer

Rows: TX1:329, TX2:212. Needs deployed None-observer erase/rename-stability certificate (ae), exact emitted trace equality and matched native controls. General Option<fn> shapes stay quarantined.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/lib.rs::first_decoded

Rows: TX1:328. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::tx1 [D SCC 210]; programs/r1-cost-probe/src/lib.rs::observer [D SCC 266].

## programs/r1-cost-probe/src/pool_route.rs::admitted

Rows: TX1:331, TX2:214. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot

Rows: TX1:343, TX2:239. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data

Rows: TX1:335, TX2:229. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key

Rows: TX1:337, TX2:231. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts

Rows: TX1:339, TX2:235. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer

Rows: TX1:340, TX2:237. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len

Rows: TX1:336, TX2:230. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner

Rows: TX1:338, TX2:232. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint

Rows: TX1:341, TX2:238. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len [D SCC 275]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner [D SCC 276].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero

Rows: TX1:342. Full Lean extracted-reference/cohort theorem NFQ_ZeroSource.source plus arbitrary-index body laws and induction PASS. K058/K059 certify a length0..4 source-cut result only; K060 pointer fact lacks its negative control. General physical length/frame/window composition and native/model association remain missing. Needs a new split native shape and matched controls, not another whole-buffer run.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned

Rows: TX1:345. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public [D SCC 247]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 [opaque S]; crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 [opaque S]; programs/r1-cost-probe/src/lib.rs::first_decoded [D SCC 267]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts [D SCC 272]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer [D SCC 274]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint [D SCC 277]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero [D SCC 278].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1

Rows: TX1:344. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot [D SCC 269]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned [D SCC 279].

## programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id

Rows: TX2:220. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box

Rows: TX2:216. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1 [D SCC 244].

## programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release

Rows: TX2:217. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical [opaque S].

## programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box

Rows: TX2:218. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1 [D SCC 246].

## programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id

Rows: TX2:225. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok

Rows: TX2:223. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: No canonical internal callee; native source/result/frame correspondence itself is still required..

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account

Rows: TX2:236. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok [D SCC 286]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner [D SCC 276].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry

Rows: TX2:234. Needs one arbitrary-prestate native iteration (or (ad) data-independent factorization after its prerequisites), matched controls, full invariant/frame induction and native/model step association. No complete native packet for this member was admitted here.

Callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 [D SCC 242]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at [D SCC 251]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at [D SCC 252]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable [D SCC 253]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused [D SCC 254]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable [D SCC 255]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused [D SCC 256]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 [D SCC 259]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 [D SCC 261]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 [D SCC 263]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 [D SCC 265]; programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id [D SCC 281]; programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id [D SCC 285]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account [D SCC 287].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts

Rows: TX2:233. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box [D SCC 282]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release [D SCC 283]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box [D SCC 284]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry [D SCC 288]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts [D SCC 272]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account [D SCC 287]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer [D SCC 274]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint [D SCC 277].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8

Rows: TX2:242. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id [D SCC 281]; programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts [D SCC 289].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned

Rows: TX2:241. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated [D SCC 240]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 [opaque S]; programs/r1-cost-probe/src/lib.rs::observer [D SCC 266]; programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 [D SCC 290].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2

Rows: TX2:240. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: crates/aspis-core/src/r0/domain.rs::FibreIndex::get [opaque Q]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot [D SCC 269]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned [D SCC 291].

## programs/r1-cost-probe/src/r1_pool_adapter.rs::process

Rows: TX1:333, TX2:221. Needs its own complete frozen-body hybrid contract/call-log gate and matched failing controls, exact existing/extracted model equality, frame/Result/effect correspondence and ax2. Prior local or WIP evidence is not a composed certificate; native budget is exhausted.

Callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 [D SCC 280]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 [D SCC 292].

## programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction

Rows: TX1:330, TX2:213. Needs native exact-slice/order/reply transport and matching corrupt-slice/reply control, then Lean substitution. Digest VALUE remains existing runtime trust; no SHA unwinding.

Callees: programs/r1-cost-probe/src/pool_route.rs::admitted [D SCC 268]; programs/r1-cost-probe/src/r1_pool_adapter.rs::process [D SCC 293].
