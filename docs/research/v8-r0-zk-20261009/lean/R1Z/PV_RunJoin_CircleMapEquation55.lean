import R1Z.PV_RunJoin_CircleMapModel55
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_RunJoin_CircleMapEquation55
open PV_RunJoin_CircleR72Carrier52
open AspisV8R19.SamplerClosureCircleSourceExecution

def decOutcome : core.result.Result OP AspisR72Sampler.circle.CirclePointError →
    core.result.Result Point Bool
  | .Ok p => .Ok (decPoint p)
  | .Err .SingularParameter => .Err false
  | .Err .ParameterInCm31Subfield => .Err true

theorem inverse (r : core.result.Result Point Bool) : decOutcome (encOutcome r)=r := by
  cases r with
  | Ok p => rfl
  | Err b => cases b <;> rfl

theorem complete (q : Q) (hc : PV_RunJoin_CircleNeutralShape53.QC q) :
    PV_RunJoin_CircleRawMap52.map_parameter q=ok (decOutcome
      (encodeResult (AspisV8R19.SamplerCirclePolicy.pureMap (PV_RunJoin_CircleParameterModel54.value q)))) := by
  obtain ⟨outcome,hr,he⟩ := PV_RunJoin_CircleMapModel55.complete q hc
  have eq := congrArg decOutcome he
  rw [inverse] at eq
  exact hr.trans (congrArg Result.ok eq)
#print axioms decOutcome
#print axioms inverse
#print axioms complete
end R1Z.PV_RunJoin_CircleMapEquation55
