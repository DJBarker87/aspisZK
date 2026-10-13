import R1AppendTreeExtraction

/-! Combined focused audit for the concrete empty table and chronological
root extension. No claim of Rust/source, shared-oracle, or privacy closure. -/
#print axioms R0P.poseidon_chain
#print axioms AspisR1.PoseidonMap.map_nodeCompress
#print axioms AspisR1.FrozenEmptyRoots.initial
#print axioms AspisR1.FrozenEmptyRoots.successor
#print axioms AspisPool.IncrementalMerkleV1.append_reconstruct_afterstate
#print axioms AspisPool.IncrementalMerkleV1.reconstruct_ofFn_chain
#print axioms AspisR1.AppendTreeRoot.frozen_recursive
#print axioms AspisR1.AppendTreeRoot.path_reconstruct
#print axioms AspisR1.AppendTreeRoot.next_root_correct
#print axioms AspisR1.AppendTreeExtraction.strengthen_candidate_result
