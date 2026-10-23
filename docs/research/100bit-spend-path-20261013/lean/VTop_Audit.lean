import VTop_Order
import VTop_Accepted

/-! Focused union/axiom audit; cached imports, not a frozen release replay. -/
#print axioms AspisR1.VTop_Accepted.accepted_run
#print axioms AspisR1.VTop_Checkpoint.writer_join
#print axioms AspisR1.VTop_Checkpoint.reader_join
#print axioms AspisR1.VTop_Cuts.writer_reached
#print axioms AspisR1.VTop_Cuts.resume_reached
#print axioms AspisR1.VTop_Entry.op10_source
#print axioms AspisR1.VTop_Entry.op11_source
#print axioms AspisR1.VTop_Entry.first_accepted
#print axioms AspisR1.VTop_Erasure.tx1_source
#print axioms AspisR1.VTop_Erasure.tx1_erasure
#print axioms AspisR1.VTop_Erasure.tx2_common_source
#print axioms AspisR1.VTop_Erasure.tx2_common_erasure
#print axioms AspisR1.VTop_Erasure.tx2_authenticated_source
#print axioms AspisR1.VTop_Erasure.tx2_authenticated_erasure
#print axioms AspisR1.VTop_Erasure.erase_pure
#print axioms AspisR1.VTop_Erasure.erase_liftM
#print axioms AspisR1.VTop_Erasure.erase_if
#print axioms VTop_Stages.verifier.candidate.tx1
#print axioms VTop_Stages.verifier.candidate.tx2_common
#print axioms VTop_Stages.verifier.candidate.tx2_authenticated
#print axioms AspisR1.VTop_Order.tx1_order
#print axioms AspisR1.VTop_Order.tx2_common_order
#print axioms AspisR1.VTop_Order.tx2_order
#print axioms AspisR1.VTop_Order.accepted_tx1
#print axioms AspisR1.VTop_Order.accepted_tx2
#print axioms AspisR1.VTop_Run.accepted_execution
#print axioms AspisR1.VTop_Run.run_bind
#print axioms AspisR1.VTop_Run.run_perform
#print axioms AspisR1.VTop_Run.run_lift
#print axioms AspisR1.VTop_Run.run_pure
#print axioms AspisR1.VTop_Run.thenResult_assoc
#print axioms AspisR1.VTop_Run.thenResult_ok
#print axioms AspisR1.VTop_SecondFlow.common_source
#print axioms AspisR1.VTop_SecondOrder.tail_order
#print axioms AspisR1.VTop_SecondOrder.common_order
#print axioms AspisR1.VTop_Trace.erase_run
#print axioms AspisR1.VTop_Trace.run_prefix
#print axioms AspisR1.VTop_Trace.erase_perform
#print axioms AspisR1.VTop_Trace.erase_lift
#print axioms AspisR1.VTop_Trace.erase_bind
#print AspisR1.VTop_Checkpoint.CheckpointSourceJoin
#print AspisR1.VTop_Checkpoint.WriterProvenance
#print AspisR1.VTop_Accepted.accepted_run
