import NNH_Stage2GuardedCut
set_option autoImplicit false
noncomputable section
namespace NNH_S5Root0Finding
open RSL RSL.TX2_241 NNH_Libraries
/-- The old guarded evaluator is not a Root0-free source of weak inputs:
its supplied canonical Dom064 already contains reader Root0. -/
theorem guarded_requires_root0 (a : Args) (env : Env)
 (p : NNH_Stage2GuardedCut.Packet a env) :
 V0.Root0 p.cut.checkpoint_data
  (slice p.cut.proof_data AFTERSTATE_BYTES (AFTERSTATE_BYTES+p.cut.validated.proof_length)) :=
 p.domain.2.2.2
#print axioms guarded_requires_root0
end NNH_S5Root0Finding
