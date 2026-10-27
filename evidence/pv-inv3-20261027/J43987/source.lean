import R1Z.PV_Inv_PreGuard
import R1Z.PV_Inv_ScanCost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_GuardTraceShape
open R0P PV_Inv_GuardSites PV_Inv_GuardAllSites
variable {K : Type} [Field K] [DecidableEq K]
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

theorem row_length (t : Trace K) (lambda : K) (b : Fin 1024) :
    (rowSites t lambda b).length = 4 := by simp [rowSites]

theorem sites_length (t : Trace K) (lambda : K) :
    (sites t lambda).length = active.length * 4 := by
  simp only [sites,List.length_flatMap]
  simp only [row_length,List.map_const',List.sum_replicate,Nat.nsmul_eq_mul]

/-- Complete list of whole-value comparison outcomes on guard success.
This is not the D159 limb/address/latency observation. -/
theorem clear_trace (t : Trace K) (lambda chi : K)
    (clear : PV_Inv_PreGuard.noPoleRef t lambda chi = true) :
    (PV_Inv_ScanCost.recorded chi true (sites t lambda)).2 =
      List.replicate (active.length * 4) true := by
  rw [PV_Inv_ScanCost.safe_values chi true (sites t lambda) clear,sites_length]

#print axioms row_length
#print axioms sites_length
#print axioms clear_trace
end R1Z.PV_Inv_GuardTraceShape
