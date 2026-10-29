import R1Z.PV_RunJoin_CircleFallbackModel55
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_RunJoin_CircleTotal55
open PV_RunJoin_CircleR72Carrier52
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerCirclePolicy AspisV8R19.SamplerClosureCircleSourceExecution

def chosen (block : Array U8 32#usize) (row : Bool) : QM31Exact :=
  let t := R0P.SemSource.qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block)
  if t.im≠0 then t else if row then R0P.SemSource.circleFallbackParameter1 else R0P.SemSource.circleFallbackParameter0

theorem complete (block : Array U8 32#usize) (row : Bool) :
    PV_RunJoin_CircleRawMap52.circle_owned block row=
      ok (decPoint (encodePoint (point (chosen block row)))) := by
  obtain ⟨q,hq,hc,hvalue⟩ := PV_RunJoin_CircleParameterModel54.complete block
  have hm := PV_RunJoin_CircleMapEquation55.complete q hc
  rw [hvalue] at hm
  let t := R0P.SemSource.qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block)
  change PV_RunJoin_CircleRawMap52.map_parameter q=ok (PV_RunJoin_CircleMapEquation55.decOutcome (encodeResult (pureMap t))) at hm
  unfold PV_RunJoin_CircleRawMap52.circle_owned
  simp only [hq,bind_tc_ok]
  by_cases hi : t.im≠0
  · rw [outside_map t hi] at hm
    dsimp only [t] at hi
    simp only [hm,PV_RunJoin_CircleMapEquation55.decOutcome,encodeResult,bind_tc_ok,chosen,if_pos hi]
  · have hz : t.im=0 := not_ne_iff.mp hi
    obtain ⟨e,he⟩ : ∃ e,pureMap t=.error e := by
      by_cases hd : 1+t^2=0
      · exact ⟨.singular,singular_first t hd⟩
      · exact ⟨.subfield,by simp only [pureMap,if_neg hd,if_pos hz]⟩
    rw [he] at hm
    dsimp only [t] at hi
    cases e <;> cases row <;>
      simp only [hm,encodeResult,encodeError,PV_RunJoin_CircleMapEquation55.decOutcome,bind_tc_ok,
        chosen,if_neg hi,Bool.false_eq_true,if_false,if_true,
        PV_RunJoin_CircleFallbackModel55.first,PV_RunJoin_CircleFallbackModel55.second]
#print axioms chosen
#print axioms complete
end R1Z.PV_RunJoin_CircleTotal55
