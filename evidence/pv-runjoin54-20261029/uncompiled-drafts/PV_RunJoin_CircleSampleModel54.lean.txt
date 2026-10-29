import R1Z.PV_RunJoin_CircleMapModel54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleSampleModel54
open PV_RunJoin_CircleR72Carrier52

theorem complete (block : Array U8 32#usize) :
    ∃ parameter outcome,
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample block=ok parameter ∧
      PV_RunJoin_CircleRawMap52.map_parameter parameter=ok outcome ∧
      encOutcome outcome=AspisV8R19.SamplerClosureCircleSourceExecution.encodeResult
        (AspisV8R19.SamplerCirclePolicy.pureMap
          (R0P.SemSource.qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block))) := by
  obtain ⟨parameter,hp,hc,hvalue⟩ := PV_RunJoin_CircleParameterModel54.complete block
  obtain ⟨outcome,ho,he⟩ := PV_RunJoin_CircleMapModel54.complete parameter hc
  rw [hvalue] at he
  exact ⟨parameter,outcome,hp,ho,he⟩
#print axioms complete
end R1Z.PV_RunJoin_CircleSampleModel54
