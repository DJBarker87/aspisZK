#!/usr/bin/env python3
"""Hash-pinned coverage ledger. Open rows are not verified certificates."""
import json,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
C='crates/aspis-r1-cost-probe/src/'
P='crates/aspis-prover/src/'
rows=[]
def add(family,file,anchor,reference,status,gap):
 s=Path(file).read_text();assert anchor in s,(family,anchor)
 rows.append(dict(family=family,source=file,source_sha256=hashlib.sha256(s.encode()).hexdigest(),anchor=anchor,line=s[:s.index(anchor)].count('\n')+1,reference=reference,status=status,remaining=gap))
add('public digest',C+'prover.rs','pub fn prove_masked_attempt(',None,'open','Inline entry-point callback has no adopted reference contract.')
add('outer private-attempt binding',C+'prover.rs','b"UNPROVED:R1:P3:PRIVATE-ATTEMPT"',None,'open','The inline call at the secure entry point has not been transported to qBind 0; fixture occurrence is not a proof.')
add('pool binding',P+'state_only_entropy.rs','pub fn pool_v1_private_attempt_binding(',['state_only_entropy::prover_commit_rom::pool_binding'],'local helper only','Entry-point binding identity, descriptor and source execution remain open.')
add('mask seed',P+'state_only_hiding.rs','fn derive_state_only_mask_seed_from_entropy_ref(',['R1Z.ProverCommitStreamSource.mask_seed'],'local helper only','Nonzero entropy, successful context encoding, actual caller invocation and global oracle history remain open.')
add('intermediate source seed',P+'state_only_entropy.rs','pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1(',None,'open','Inline POOL_V1_SOURCE_SEED_DOMAIN call after material build has no adopted verified reference contract.')
add('D seed',P+'state_only_entropy.rs','fn derive_pool_v1_zero_factor_d(',None,'open','Inline POOL_V1_D_SEED_DOMAIN call has no adopted verified reference contract.')
add('mask stream',P+'state_only_hiding.rs','fn next_word(&mut self)', ['state_only_hiding::callsite12::mask_iteration','R1Z.ProverCommitShippedTransport.mask_scalar_transport'],'local helper and conditional composition','Material-builder collection, concrete step-law instance and call-state invariants remain open.')
add('source/D stream',P+'state_only_entropy.rs','fn next_word(&mut self)', ['state_only_entropy::callsite12::source_iteration','R1Z.ProverCommitShippedTransport.source_scalar_transport'],'local helper and conditional composition','D builder collection, concrete step-law instance and call-state invariants remain open.')
add('reserved leaf salts',P+'state_only_entropy.rs','pub fn derive_pool_v1_leaf_salt(', ['state_only_entropy::prover_commit_rom::pool_leaf_salt','R1Z.ProverCommitSaltSource.salt_source'],'local helper only','derive_private_salts loop and each tree/index/retained reserved-state instance remain open.')
add('packed C1/C2 leaves',C+'host_commitment.rs','fn build(',['prover_commit_oracle::selected_c1_leaf_frame','prover_commit_oracle::selected_c2_leaf_frame','R1Z.ProverCommitGrammarSource.leaf_gram'],'local leaf helper only','Actual packed-lane traversal, value-image and per-leaf salt identities remain open.')
add('folded leaves including zero padding',C+'prover.rs','fn prove_from_semantics(',['prover_commit_oracle::private_leaf_folded','R1Z.ProverCommitGrammarSource.leaf_gram'],'local leaf helper only','Folded-word/padding loop, indices and retained salt identities remain open.')
add('binary nodes',C+'multiproof.rs','pub fn binary_parent<',['multiproof::callbacks12::node'],'local framing only','Tree construction loop, ordered children and same retained hash backend remain open.')
add('semantic transcript initialization',C+'r1_wire.rs','pub fn new(hash: H, public_bytes:', ['r1_wire::callbacks12::semantic_new'],'local framing only','Public-byte length bound 4096 is explicit; concrete caller bytes, root and same global oracle remain open.')
add('semantic absorb/squeeze/advance and row-order rejection',C+'r1_wire.rs','fn sample_block_validated(',['r1_wire::callbacks12::validated_block'],'local framing only','Validated-record construction, row schedule, samplers and complete history remain open. Framed bound 3717 and row<=26 are explicit.')
add('outer transcript initialization',C+'transcript.rs','pub fn new(hash:H,', ['transcript::callbacks12::new_transcript'],'local framing only','Semantic-state image and shared callback identity remain open; harness fixes S2.')
add('outer absorb/squeeze/advance',C+'transcript.rs','pub fn absorb(',['transcript::callbacks12::absorb','transcript::callbacks12::block'],'local framing only','Scalar sampler, payload image and global oracle history remain open; payload<=2048 and row<=32 are explicit.')
add('query blocks and advances',C+'transcript.rs','pub fn queries(',['transcript::callbacks12::queries_prefix'],'literal prefix only','Seventeen-read prefix framing and both answer buffers are checked; full queries_from_pairs/result-state transport and next rho call remain open. The whole-sampler probe was stopped, not adopted.')
add('retry/abort histories',C+'prover.rs','pub fn prove_masked_retrying_with(',None,'open','Whole attempt order, fresh secrets, reserve/abort effects and retained cross-attempt oracle history have no adopted source join.')
(E/'callback-coverage.json').write_text(json.dumps(dict(kind='coverage ledger, not a whole-source certificate',source_revision='3ac016af1',all_family_coverage_closed=False,rows=rows),indent=2)+'\n')
