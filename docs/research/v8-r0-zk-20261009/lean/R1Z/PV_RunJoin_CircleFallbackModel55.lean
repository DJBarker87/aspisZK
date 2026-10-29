import R1Z.PV_RunJoin_CircleMapEquation55
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_RunJoin_CircleFallbackModel55
open PV_RunJoin_CircleR72Carrier52 PV_RunJoin_CircleNeutralShape53
open AspisV8R19.SamplerClosureCircleSourceExecution AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerClosureProductCorrectness

def parameter0 : Q := ((0#u32,0#u32),(1#u32,0#u32))
def parameter1 : Q := ((1#u32,0#u32),(1#u32,0#u32))
theorem value0 : PV_RunJoin_CircleParameterModel54.value parameter0=R0P.SemSource.circleFallbackParameter0 := by rfl
theorem value1 : PV_RunJoin_CircleParameterModel54.value parameter1=R0P.SemSource.circleFallbackParameter1 := by rfl

theorem first : PV_RunJoin_CircleRawMap52.fallback 0#usize=
    ok (decPoint (encodePoint (point R0P.SemSource.circleFallbackParameter0))) := by
  have hm := PV_RunJoin_CircleMapEquation55.complete parameter0 (show QC parameter0 from ⟨czero,cone⟩)
  rw [value0,outside_map _ (show R0P.SemSource.circleFallbackParameter0.im≠0 by exact one_ne_zero)] at hm
  unfold PV_RunJoin_CircleRawMap52.fallback
  have hrem : (0#usize%2#usize)=ok 0#usize := rfl
  have hidx : Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK 0#usize=ok parameter0 := rfl
  simp only [hrem,hidx,bind_tc_ok,hm,PV_RunJoin_CircleMapEquation55.decOutcome,encodeResult]
  rfl

theorem second : PV_RunJoin_CircleRawMap52.fallback 1#usize=
    ok (decPoint (encodePoint (point R0P.SemSource.circleFallbackParameter1))) := by
  have hm := PV_RunJoin_CircleMapEquation55.complete parameter1 (show QC parameter1 from ⟨cone,cone⟩)
  rw [value1,outside_map _ (show R0P.SemSource.circleFallbackParameter1.im≠0 by exact one_ne_zero)] at hm
  unfold PV_RunJoin_CircleRawMap52.fallback
  have hrem : (1#usize%2#usize)=ok 1#usize := rfl
  have hidx : Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK 1#usize=ok parameter1 := rfl
  simp only [hrem,hidx,bind_tc_ok,hm,PV_RunJoin_CircleMapEquation55.decOutcome,encodeResult]
  rfl
#print axioms parameter0
#print axioms parameter1
#print axioms value0
#print axioms value1
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleFallbackModel55
