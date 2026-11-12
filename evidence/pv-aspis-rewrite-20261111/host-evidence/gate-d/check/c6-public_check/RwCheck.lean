import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- block emitted by tool k2 (7271db7e), sha256 cdbbfe17c2bc9fd4a7714bcb12dd272f5f8061b06ae7c6eca609d8c1c16fd2ff, source ['src/prover.rs', 548, 565]
def prover.public_check
  (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize)
  (times : alloc.vec.Vec aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes)
  :
  Result ((core.result.Result Unit verifier.Error) × (alloc.vec.Vec
    aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes))
  := do
  let b ←
    core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant variant
      transport.Variant.S2
  if b
  then ok (core.result.Result.Err verifier.Error.Semantic, times)
  else
    let (accepted, check_times) ←
      aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check challenges
    let times1 ← alloc.vec.Vec.push times check_times
    if accepted
    then ok (core.result.Result.Ok (), times1)
    else ok (core.result.Result.Err verifier.Error.Rejected, times1)

end
end RW
end ProverPin2

example : type_of% @ProverPin2.RW.prover.public_check = type_of% @ProverPin2.prover.public_check := rfl
#check @ProverPin2.RW.prover.public_check
#print axioms ProverPin2.RW.prover.public_check
-- 1 carried blocks, 0 new opaque items, 1 signature checks
