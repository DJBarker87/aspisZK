import Port4B_StageRows
import Port4B_Audit

/-! Final FOCUSED union, not a frozen release replay. The concrete S1
PreparedBinding instance and parser/model provenance remain explicit.
All owned key/count/slot/verifier adapters retain named P6 source lowering;
this file does not promote them to fresh native extractions or ELF proofs. -/
#print AspisR1.Port4B_Install.leaves
#print AspisR1.Port4B_StageRows.PreparedBinding
#print AspisR1.Port4B_CallerJoin.accepted
#print AspisR1.Port4B_StageRows.tx1
#print AspisR1.Port4B_StageRows.tx2
#print axioms AspisR1.Port4B_Install.installation
#print axioms AspisR1.Port4B_KeyInstall.packed
#print axioms AspisR1.Port4B_LeafLoop.accepted
#print axioms AspisR1.Port4B_Padding.native_zero
#print axioms AspisR1.Port4B_VerifyRun.accepted
#print axioms AspisR1.Port4B_TailRun.accepted
#print axioms AspisR1.Port4B_TreeJoin.accepted
#print axioms AspisR1.Port4B_BatchJoin.accepted
#print axioms AspisR1.Port4B_CallerJoin.accepted
#print axioms AspisR1.Port4B_Prepared.roots
#print axioms AspisR1.Port4B_Prepared.query_value
#print axioms AspisR1.Port4B_FoldedCut.model
#print axioms AspisR1.Port4B_PrepareCut.tx1
#print axioms AspisR1.Port4B_StageRows.tx1
#print axioms AspisR1.Port4B_StageRows.tx2
#print axioms AspisR1.MultiproofConeP6Frozen2Stage.both_batches
