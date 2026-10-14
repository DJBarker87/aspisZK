import R1OracleVerifier
import R1Merkle32Path
import R1Merkle32Leaf

/-! A focused public-axiom audit of the generic verifier/oracle bridge and
Merkle32 path and leaf lemmas, including the four checked input lengths. This
module adds no source correspondence or security conclusion. -/

#print axioms AspisR1.OracleVerifier.verifierFrom_eval
#print axioms AspisR1.OracleVerifier.verifier_eval
#print axioms AspisR1.OracleVerifier.verifier_chain_reads
#print axioms AspisR1.OracleVerifier.verifier_terminal_reads
#print axioms AspisR1.OracleVerifier.verifier_specializes_done

#print axioms AspisR1.Merkle32Path.nodeInput_length
#print axioms AspisR1.Merkle32Path.nodeBytes_injective
#print axioms AspisR1.Merkle32Path.nodeInput_injective
#print axioms AspisR1.Merkle32Path.fillChild_ne
#print axioms AspisR1.Merkle32Path.nodeInput_ne_of_current_ne
#print axioms AspisR1.Merkle32Path.foldPath_cross_trace_collision
#print axioms AspisR1.Merkle32Path.foldPath_injective_of_collisionFreeOn
#print axioms AspisR1.Merkle32Path.depth6_cross_trace_collision

#print axioms AspisR1.Merkle32Leaf.leafInput_fixedWidth_injective
#print axioms AspisR1.Merkle32Leaf.leaf_path_binding
#print axioms AspisR1.Merkle32Leaf.c1_leaf_path_binding
#print axioms AspisR1.Merkle32Leaf.c2_leaf_path_binding
#print axioms AspisR1.Merkle32Leaf.folded_leaf_path_binding
#print axioms AspisR1.Merkle32Leaf.leaf_input_length
#print axioms AspisR1.Merkle32Leaf.c1_leafInput_length
#print axioms AspisR1.Merkle32Leaf.c2_leafInput_length
#print axioms AspisR1.Merkle32Leaf.folded_leafInput_length
