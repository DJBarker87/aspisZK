import NNH_Stage2GuardedEval
import LIBB_PoolScan
import LIBB_PoolReconstruct
set_option autoImplicit false
noncomputable section
namespace NNY_JunkAudit
open RSL NNH_Libraries
abbrev value := NNH_Stage2GuardedEval.value
/-- Use the existing error-choice evaluator, leaving the frozen Ref unchanged. -/
theorem returned (a : TX2_241.Args) (env : Env) :
 NND_Returned.Returns (TX2_241.Ref L D V0 a) env (value a env) :=
 NNH_Stage2GuardedEval.returned a env
/-- Off-domain 064 calls cannot create a spurious successful continuation. -/
theorem auth_domain (p q r : Bytes) (env : Env)
 (h : NNH_Stage2GuardedEval.guard p q r env = .ok ()) :
 TX2_241.Dom064 V0 (p,q,r) ∧ authValues.auth p q r env = .ok () :=
 NNH_Stage2GuardedEval.guard_ok p q r env h
/-- The scanner's panic branch chooses an error. -/
theorem scan_panic (data : Bytes) (h : ¬ data.length ≤ Aeneas.Std.Usize.max) :
 LIBB_PoolScan.evaluator data = .error .invalidAccountData := by
 unfold LIBB_PoolScan.evaluator
 rw [dif_neg h]
/-- Reconstruction's missing inverse carrier chooses an error. -/
theorem reconstruct_panic (q : LIBB_PoolCarriers.Request) (a : Authenticated)
 (c : LIBB_PoolCarriers.Afterstate) (h : LIBB_AuthCarrier.raw a = none) :
 LIBB_PoolReconstruct.evaluator q a c = .error .invalidAccountData := by
 unfold LIBB_PoolReconstruct.evaluator
 rw [h]
#print axioms returned
#print axioms auth_domain
#print axioms scan_panic
#print axioms reconstruct_panic
end NNY_JunkAudit
