import R1Z.PV_Inv_GuardTraceShape
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardTracePair
open R0P PV_Inv_GuardAllSites
attribute [local irreducible] sites active PV_Inv_ScanCost.recorded
variable {K : Type} [Field K] [DecidableEq K]

/-- Two successful model scans have the same sequence of whole-value Boolean
outcomes, even for different witnesses and challenges. Operand-limb tests and
machine latency are deliberately not identified with this Boolean list. -/
theorem same_clear_trace (t0 t1 : Trace K) (lambda0 lambda1 chi0 chi1 : K)
    (clear0 : PV_Inv_PreGuard.noPoleRef t0 lambda0 chi0 = true)
    (clear1 : PV_Inv_PreGuard.noPoleRef t1 lambda1 chi1 = true) :
    (PV_Inv_ScanCost.recorded chi0 true (sites t0 lambda0)).2 =
      (PV_Inv_ScanCost.recorded chi1 true (sites t1 lambda1)).2 := by
  rw [PV_Inv_GuardTraceShape.clear_trace t0 lambda0 chi0 clear0,
      PV_Inv_GuardTraceShape.clear_trace t1 lambda1 chi1 clear1]

#print axioms same_clear_trace
end R1Z.PV_Inv_GuardTracePair
