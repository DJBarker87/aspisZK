import R1Z.PV_W_ResumeAudit
set_option autoImplicit false
/- One final focused import/axioms replay. No frozen deployment manifest claim. -/
#check R1Z.PV_RunJoin_NativeEffectInterface.Identity
#check R1Z.PV_RunJoin_NativeEffectTransport.permitted
#print axioms R1Z.PV_W_Enriched.witness_representable
#print axioms R1Z.PV_W_ReservationThreading.source_complete
#print axioms R1Z.PV_W_TypedThreading.reservation_threads
#print axioms R1Z.PV_W_EntryThreading.entry_source
#print axioms R1Z.PV_W_OsCombined.reservation_os
#print axioms R1Z.PV_W_RepeatFile.repeated_exact
