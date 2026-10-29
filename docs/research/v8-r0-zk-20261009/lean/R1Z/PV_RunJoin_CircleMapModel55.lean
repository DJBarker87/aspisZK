import R1Z.PV_RunJoin_CircleR72MapAdapter54
import R1Z.PV_RunJoin_CircleParameterModel54
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleMapModel55
open PV_RunJoin_CircleR72Carrier52

theorem native_canonical (q : Q) (hc : PV_RunJoin_CircleNeutralShape53.QC q) :
    AspisV8R19.SamplerClosureProductCorrectness.Canonical (encQ q) := by
  exact ⟨hc.1.1,hc.1.2,hc.2.1,hc.2.2⟩
#print axioms native_canonical

theorem complete (q : Q) (hc : PV_RunJoin_CircleNeutralShape53.QC q) :
    ∃ outcome, PV_RunJoin_CircleRawMap52.map_parameter q=ok outcome ∧
      encOutcome outcome=AspisV8R19.SamplerClosureCircleSourceExecution.encodeResult
        (AspisV8R19.SamplerCirclePolicy.pureMap (PV_RunJoin_CircleParameterModel54.value q)) := by
  have nativeCanon : AspisV8R19.SamplerClosureProductCorrectness.Canonical (encQ q) := native_canonical q hc
  have model := AspisV8R19.SamplerClosureCircleSourceExecution.source_execution (encQ q) nativeCanon
  have assoc := PV_RunJoin_CircleR72MapAdapter54.complete q hc
  have run := assoc.symm.trans model
  obtain ⟨outcome,hr,henc⟩ := PV_RunJoin_ResultPost.bind_eq_ok run
  exact ⟨outcome,hr,Result.ok.inj henc⟩
#print axioms complete
end R1Z.PV_RunJoin_CircleMapModel55
