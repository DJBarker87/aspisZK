import R1Z.PV_RJDec_AxiomsAudit
set_option autoImplicit false
-- Focused replay of the delivered statements, not a frozen release replay.
#check @R1Z.PV_RJDec_Factor.exists_iff
#check @R1Z.PV_RJDec_ResultCases.fibres_iff
#check @R1Z.PV_RJDec_MemoryReserve.complete
#check @R1Z.PV_RJDec_MemoryDrop.complete
#check @R1Z.PV_RJDec_MemoryZero.complete
#check @R1Z.PV_RJDec_ZeroizeFinding.byte_fence_mismatch
#check @R1Z.PV_RJDec_ZeroizeFinding.array32_fence_mismatch
#print axioms R1Z.PV_RJDec_Factor.exists_iff
#print axioms R1Z.PV_RJDec_MemoryReserve.complete
#print axioms R1Z.PV_RJDec_ZeroizeFinding.byte_fence_mismatch
