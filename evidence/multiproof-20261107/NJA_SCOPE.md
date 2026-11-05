# NJA scope — stage 0

Target not yet established. Baseline NIU: 432 CLOSED / 0 QUALIFIED / 167 OPEN; all 28 assigned occurrences remain OPEN. Full original row records, frozen body hashes, discovery evidence, and caller clauses are retained without omission in NJA_TARGET_ROWS.json.xz. No inventory evidence receives proof credit.

## Model owners and domains

Multiproof: adopted binary cohort MultiproofConeRef.reference, consumed by MultiproofConeP6Frozen2Stage.sourceBatch / sequence and MultiproofConeP6Callbacks. Source scalar helpers have inlined consumers rather than named cohort helpers; exact association must be proved, not inferred from names. The eight-way-only value_at has no reached binary consumer (NDT rejection); unresolved domain/reachability finding. Poseidon: R0P.poseidonPow5 / poseidonMat4 / poseidonExternalLinear / poseidonInternalLinear / poseidonPermutation in R0P.Poseidon (generic Field, specialized to M31). The native M31 carrier, actual trace association and v3 compression caller remain to prove. Do not substitute state_only_poseidon (QM31) for this M31 module.

TX1/TX2 non-generic multiproof functions have identical frozen bodies and signatures. Digest parents/verify_in_place share generic source but require deployed SolanaDigest instance pinning before claiming identical monomorphization. Per-occurrence obligations differ: TX1 <=10 entries; TX2 <=12, same 16-cell buffers. Every occurrence remains separately checked.

## TX1:118 crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits

Frozen body SHA256: `546a480c2596f8e9ed19c455aaeaadf0140c9e2b4edf4a3c853d3757178c7010`. Obligation hash: `7d8d223e42f7c9822414a6c2455eb8d95d2e7dc028730f2831df534b0c41d5e6`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX1:119 crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels

Frozen body SHA256: `c930a78a1df8a23cf99e48e2bf88eb1449453f4c9f0588a0ea99ba53b09583e3`. Obligation hash: `b45dff2dd8d8a7c5eab18664186322d9fe40cf97b4a8756b0b12aa86b4cfbd7d`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX1:120 crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width

Frozen body SHA256: `4cb585a215a0dface45ee399077ff62b3fad5aec8ea5c93e0f24a2ef5671b14c`. Obligation hash: `fcbf24aa02731f4146f45275b5e13a6b7f959b8149a372b88c8640fcab667418`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX1:121 crates/aspis-r1-cost-probe/src/multiproof.rs::index_at

Frozen body SHA256: `fb50c5eb22c58411bca20dff8dc5854399b405e88591982a0525c1e214c2ae4e`. Obligation hash: `7aa311c150cdc9389ae0e251274bf078afd50796dd4f34b88d455f4685095d0b`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX1:122 crates/aspis-r1-cost-probe/src/multiproof.rs::node_count

Frozen body SHA256: `19c689b177eaa992ec60264993d47d5880fe5d07ad77b12c682ff7a8c528967e`. Obligation hash: `b25e7e6bfa6acf6581cbeda6c1e5a2bea445e5359feb3cb8cd13f62c921060e6`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::index_at [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed [OPEN].

Caller obligations: 9; exact clauses retained in the row snapshot. No clause discharged.

## TX1:123 crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent

Frozen body SHA256: `9682d654cd2640087b4b06be05503cb2f9a8ab282fdebe0d70621b976482da39`. Obligation hash: `d8b8b0171d9fa2d37e802f733e59dbb278da2521e5a11f4d834f38a94e48af2a`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [CLOSED].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX1:124 crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches

Frozen body SHA256: `c879f9d0a00520505a521c6e186888ca23d1f2fccbe63bb1bdefe9f468876e35`. Obligation hash: `95465c8ef516fd53e94e04ff9f4321aa37efc46efd6e70a88f802df0706631a0`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX1:125 crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent

Frozen body SHA256: `ce4a228046a9684d22a6572edd7253118eb5631c05d39fe59b10db1b571a907c`. Obligation hash: `68ec025ff5551860daca9d4d666d0c464b792e34dcb6d7be376dd2bd9afd45a1`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [CLOSED].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX1:126 crates/aspis-r1-cost-probe/src/multiproof.rs::value_at

Frozen body SHA256: `4574347385146c0b5a87239076136f997176576f5c9b0d30e82de1e1d74c43be`. Obligation hash: `54a236d366feaf49fa4ec18fcb0ed6c3c67af735bc18b7ec84584b9dbae97c49`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX1:127 crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place

Frozen body SHA256: `cc8c08dc90a3b055e66141f3e0d9b67ba3df8fd7ea2f55e031e4bbe13d718c63`. Obligation hash: `7bb3d8db80110e5cc21d1c8ecaec3fca51309a298c1920dbe82b1102332a1972`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: crates/aspis-core/src/r0/merkle.rs::parent_with_digest [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::index_at [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::value_at [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed [OPEN].

Caller obligations: 16; exact clauses retained in the row snapshot. No clause discharged.

## TX1:128 crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed

Frozen body SHA256: `9e2022011570854c66e81e8eb3a4f80df19ef43ee17011aeb90ef99cfd89d06f`. Obligation hash: `fe7950a2dbb0f18b73e1adad06a4caed856656d3fd52330f6f4edb29ab46b09d`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.

Callees: none.

Caller obligations: 6; exact clauses retained in the row snapshot. No clause discharged.

## TX1:302 crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy

Frozen body SHA256: `593f9015765e3d52eb07a324b690118f3a5c7755c4d82908bf44e7d0fa9ebd22`. Obligation hash: `b8a3bd6790982e445e6dd2131a4befc056400a1e6a45eb18c057a0c8992e20ed`.

Model: R0P.Poseidon scalar definitions, specialized to M31 (not the QM31 state-only helper). Exact native carrier and per-row trace/v3 input association remain OPEN; extraction selected none.

Inventory domain: Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.

Callees: crates/aspis-core/src/field.rs::M31::reduce_u62 [CLOSED].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX1:303 crates/aspis-statement/src/poseidon2.rs::external_linear_lazy

Frozen body SHA256: `b5712d6cf182a1fbee7c6767db0b74a5ae1616bcb32aaf5ad4ee23cf09000e4f`. Obligation hash: `b4487e182cfac07c92c1af1197c623c00e663cf68932bb3f3002101c3865bbd3`.

Model: R0P.Poseidon scalar definitions, specialized to M31 (not the QM31 state-only helper). Exact native carrier and per-row trace/v3 input association remain OPEN; extraction selected none.

Inventory domain: Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.

Callees: crates/aspis-core/src/field.rs::M31::reduce_u62 [CLOSED]; crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy [OPEN].

Caller obligations: 8; exact clauses retained in the row snapshot. No clause discharged.

## TX1:304 crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy

Frozen body SHA256: `9a32cc3ce561c7abcf77fb1884e7a5e6ac64c73087eb6be2be06caef21c6d6a5`. Obligation hash: `979b2f846aaba38aa3470487be0e21140b6ddb842acac89ef0e847d8eba65e07`.

Model: R0P.Poseidon scalar definitions, specialized to M31 (not the QM31 state-only helper). Exact native carrier and per-row trace/v3 input association remain OPEN; extraction selected none.

Inventory domain: Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.

Callees: crates/aspis-core/src/field.rs::M31::reduce_u62 [CLOSED].

Caller obligations: 4; exact clauses retained in the row snapshot. No clause discharged.

## TX1:305 crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3

Frozen body SHA256: `476491f4cb87936f2538797bc45399703339d999858615dcae906fd9074a059b`. Obligation hash: `e361522da82418df59d88c502bed9260598aed125ca08dd719384ba1d4e09ff0`.

Model: R0P.Poseidon scalar definitions, specialized to M31 (not the QM31 state-only helper). Exact native carrier and per-row trace/v3 input association remain OPEN; extraction selected none.

Inventory domain: Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.

Callees: crates/aspis-core/src/field.rs::CM31::add [CLOSED]; crates/aspis-core/src/field.rs::M31::add [CLOSED]; crates/aspis-core/src/field.rs::QM31::add [CLOSED]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [CLOSED]; crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace [OPEN].

Caller obligations: 8; exact clauses retained in the row snapshot. No clause discharged.

## TX1:306 crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace

Frozen body SHA256: `bb51cc19d0611b8808c6ae0a7cb8100ce74a9f532ade5878177b602c9a16ab91`. Obligation hash: `95c786af78eb4db75f97a3e5fb890fd7dca4fe4936dcd32fae7a52dff268cb9e`.

Model: R0P.Poseidon scalar definitions, specialized to M31 (not the QM31 state-only helper). Exact native carrier and per-row trace/v3 input association remain OPEN; extraction selected none.

Inventory domain: Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.

Callees: crates/aspis-core/src/field.rs::CM31::add [CLOSED]; crates/aspis-core/src/field.rs::M31::add [CLOSED]; crates/aspis-core/src/field.rs::QM31::add [CLOSED]; crates/aspis-core/src/field/wide_exact.rs::WideExact::add [CLOSED]; crates/aspis-statement/src/poseidon2.rs::external_linear_lazy [OPEN]; crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy [OPEN]; crates/aspis-statement/src/poseidon2.rs::pow5 [OPEN].

Caller obligations: 22; exact clauses retained in the row snapshot. No clause discharged.

## TX1:307 crates/aspis-statement/src/poseidon2.rs::pow5

Frozen body SHA256: `2aa900ce6bde046971ed173f7a26cadcfadb9d86de5711854efb9c2c93f064e3`. Obligation hash: `c78e3e5325b2162f0003bc2cca9ddbbe2053cdee707ab253e94be45c3031312c`.

Model: R0P.Poseidon scalar definitions, specialized to M31 (not the QM31 state-only helper). Exact native carrier and per-row trace/v3 input association remain OPEN; extraction selected none.

Inventory domain: Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.

Callees: crates/aspis-core/src/field.rs::CM31::mul [CLOSED]; crates/aspis-core/src/field.rs::M31::mul [CLOSED]; crates/aspis-core/src/field.rs::QM31::mul [CLOSED]; crates/aspis-core/src/field/wide_exact.rs::WideExact::mul [CLOSED].

Caller obligations: 4; exact clauses retained in the row snapshot. No clause discharged.

## TX2:084 crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits

Frozen body SHA256: `546a480c2596f8e9ed19c455aaeaadf0140c9e2b4edf4a3c853d3757178c7010`. Obligation hash: `28561804404e9dcffa6f1b12dc47a4c334e3681ffb22fa02cee29148c48f69db`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX2:085 crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels

Frozen body SHA256: `c930a78a1df8a23cf99e48e2bf88eb1449453f4c9f0588a0ea99ba53b09583e3`. Obligation hash: `290900092d430fe9442e70a60bd051d38530d599459d92b9e4ac33cb2dd2aae6`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX2:086 crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width

Frozen body SHA256: `4cb585a215a0dface45ee399077ff62b3fad5aec8ea5c93e0f24a2ef5671b14c`. Obligation hash: `f378ed01874456f791e329a731710242a41b225239ab7d60cc6f490fcae30515`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN].

Caller obligations: 1; exact clauses retained in the row snapshot. No clause discharged.

## TX2:087 crates/aspis-r1-cost-probe/src/multiproof.rs::index_at

Frozen body SHA256: `fb50c5eb22c58411bca20dff8dc5854399b405e88591982a0525c1e214c2ae4e`. Obligation hash: `989cd8021843def524578df5271d16ac93927535063ca9f34ce9fdd4424bce0b`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX2:088 crates/aspis-r1-cost-probe/src/multiproof.rs::node_count

Frozen body SHA256: `19c689b177eaa992ec60264993d47d5880fe5d07ad77b12c682ff7a8c528967e`. Obligation hash: `089b8151538e81aa738b7dda53d0e9dff152ea5687dc4f911a3d623a234304f9`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::index_at [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed [OPEN].

Caller obligations: 9; exact clauses retained in the row snapshot. No clause discharged.

## TX2:089 crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent

Frozen body SHA256: `9682d654cd2640087b4b06be05503cb2f9a8ab282fdebe0d70621b976482da39`. Obligation hash: `4a8994afe1e21d2134fad99220469cd72992897b7361b59fb502b05ea05cf8b4`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [CLOSED].

Caller obligations: 2; exact clauses retained in the row snapshot. No clause discharged.

## TX2:090 crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches

Frozen body SHA256: `c879f9d0a00520505a521c6e186888ca23d1f2fccbe63bb1bdefe9f468876e35`. Obligation hash: `8bb1738b6cc7975b6016a45fed34a2f2a8e17a110b548ba30247164bcb24c89e`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX2:091 crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent

Frozen body SHA256: `ce4a228046a9684d22a6572edd7253118eb5631c05d39fe59b10db1b571a907c`. Obligation hash: `b42d27890f0dac17002afa8361e22c9e7e5ff030017736443f62633ba59fdd7d`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [CLOSED].

Caller obligations: 3; exact clauses retained in the row snapshot. No clause discharged.

## TX2:092 crates/aspis-r1-cost-probe/src/multiproof.rs::value_at

Frozen body SHA256: `4574347385146c0b5a87239076136f997176576f5c9b0d30e82de1e1d74c43be`. Obligation hash: `63d4a20ed0158dd15cb34cf29073ec45df498938ccd0689bbfc6b243f11915bb`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: none.

Caller obligations: 0; exact clauses retained in the row snapshot. No clause discharged.

## TX2:093 crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place

Frozen body SHA256: `cc8c08dc90a3b055e66141f3e0d9b67ba3df8fd7ea2f55e031e4bbe13d718c63`. Obligation hash: `9e60cb3b5406e96a1cf713311d1b83e5ebaae08f5921278dbbd414d2630bbc43`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: crates/aspis-core/src/r0/merkle.rs::parent_with_digest [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::index_at [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::value_at [OPEN]; crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed [OPEN].

Caller obligations: 17; exact clauses retained in the row snapshot. No clause discharged.

## TX2:094 crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed

Frozen body SHA256: `9e2022011570854c66e81e8eb3a4f80df19ef43ee17011aeb90ef99cfd89d06f`. Obligation hash: `e4a359c202d2421671bc228d95554f42e3110944ef04dd9b29ab6dd6f5310522`.

Model: MultiproofConeRef.reference binary inlined consumer; association OPEN.

Inventory domain: proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.

Callees: none.

Caller obligations: 6; exact clauses retained in the row snapshot. No clause discharged.
