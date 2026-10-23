import S2W_Audit
import S2W_Observation
import S2W_ChildTrace

/- Focused union audit; no frozen-manifest or native closure claim. -/
#print axioms AspisR1.S2W_Trace.erase_run
#print axioms AspisR1.S2W_Trace.run_prefix
#print axioms AspisR1.S2W_Trace.erase_perform
#print axioms AspisR1.S2W_Trace.erase_lift
#print axioms AspisR1.S2W_Trace.erase_bind
#print axioms AspisR1.S2W_Outer.stage1_source
#print axioms AspisR1.S2W_Outer.stage2_source
#print axioms AspisR1.S2W_OuterErasure.erase_mapError
#print axioms AspisR1.S2W_OuterErasure.first_erasure
#print axioms AspisR1.S2W_OuterErasure.erase_pure
#print axioms AspisR1.S2W_OuterErasure.erase_liftM
#print axioms AspisR1.S2W_OuterErasure.erase_if
#print axioms AspisR1.S2W_OuterErasure.stage1_erasure
#print axioms AspisR1.S2W_OuterErasure.stage2_erasure
#print axioms AspisR1.S2W_TraceFacts.success_exists
#print axioms AspisR1.S2W_TraceFacts.run_valid
#print axioms AspisR1.S2W_TraceFacts.run_bind
#print axioms AspisR1.S2W_Observation.erasure
#print axioms AspisR1.S2W_Observation.accepted_observation
#print axioms AspisR1.S2W_Observation.accepted_segments
#print axioms AspisR1.S2W_ChildTrace.perform_return
#print axioms AspisR1.S2W_ChildTrace.first_return
#print axioms _private.S2W_OuterErasure.0.AspisR1.S2W_OuterErasure.bind_congr
