import R1C1PartialCandidates
import R1C1TableStability
import R1LaterTableStability

/-! Focused axioms checkpoint for table-independent committed recovery and
the existing C1 candidate bound. No knowledge, privacy, or source-refinement
claim is introduced by this checkpoint. -/

#print axioms AspisR1.C1PartialCandidates.mem_c1Lanes
#print axioms AspisR1.C1PartialCandidates.candidates_card
#print axioms AspisR1.C1PartialCandidates.candidates_eq_of_selected_eq
#print axioms AspisR1.C1PartialCandidates.projected_full_mem
#print axioms AspisR1.MerkleNodeLookupExt.lookup_eq
#print axioms AspisR1.MerkleNodeLookupExt.walk_eq
#print axioms AspisR1.MerkleLeafLookupExt.lookupLeaf_some_iff
#print axioms AspisR1.MerkleLeafLookupExt.lookupLeaf_eq
#print axioms AspisR1.MerkleNodeRecordUnique.nodes_unique_by_digest
#print axioms AspisR1.MerkleLeafRecordUnique.leaves_digest_unique
#print axioms AspisR1.MerkleLogExt.nodes_mem_eq
#print axioms AspisR1.MerkleLogExt.leaves_mem_eq
#print axioms AspisR1.MerkleLogExt.recover_eq
#print axioms AspisR1.TraceTable.replay_append
#print axioms AspisR1.TraceTable.replay_empty_apply
#print axioms AspisR1.TraceTable.tableBefore_cut
#print axioms AspisR1.TraceTableMembership.mem_iff_replay_some
#print axioms AspisR1.TraceTableMembership.mem_eq_of_replay_eq
#print axioms AspisR1.CanonicalLogMembership.mem_byteLog
#print axioms AspisR1.CanonicalLogMembership.byteLog_mem_eq
#print axioms AspisR1.FirstReadCut.first_read_cut
#print axioms AspisR1.FirstReadCut.tableBefore_representation
#print axioms AspisR1.CanonicalLogSeparation.separated
#print axioms AspisR1.CanonicalLogSeparation.self_separated
#print axioms AspisR1.CanonicalTableRecovery.recover_eq_of_replay_eq
#print axioms AspisR1.CanonicalTableRecovery.represented_before_cut
#print axioms AspisR1.C1TableStability.c1_table_word_stable
#print axioms AspisR1.C1TableStability.c1_table_word_of_read
#print axioms AspisR1.LaterTableStability.c2_table_word_of_read
#print axioms AspisR1.LaterTableStability.folded_table_word_of_read
