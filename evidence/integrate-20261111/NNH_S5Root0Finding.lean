import NNH_Stage2GuardedCut
set_option autoImplicit false
noncomputable section
namespace NNH_S5Root0Finding
open RSL RSL.TX2_241 NNH_Libraries
/-- Dom064 contains reader Root0, independently of any implementation. -/
theorem domain_root0 (V : V2Lib) (pub proof ck : Bytes)
 (domain : Dom064 V (pub,proof,ck)) : V.Root0 ck proof := domain.2.2.2
/-- The old guarded-input packet explicitly carries this canonical domain;
it cannot serve as the planned Root0-free producer. -/
theorem guarded_domain (a : Args) (env : Env) (p : NNH_Stage2GuardedCut.Packet a env) :
 Dom064 V0 (p.cut.public_bytes,
  slice p.cut.proof_data AFTERSTATE_BYTES (AFTERSTATE_BYTES+p.cut.validated.proof_length),p.cut.checkpoint_data) := p.domain
#print axioms domain_root0
#print axioms guarded_domain
end NNH_S5Root0Finding
