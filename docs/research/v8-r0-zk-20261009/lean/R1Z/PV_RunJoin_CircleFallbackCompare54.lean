import R1Z.PV_RunJoin_CircleFallbackPrograms54
import R1Z.PV_RunJoin_CircleMapCanonical54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleFallbackCompare54
open PV_RunJoin_CircleNeutralShape53

theorem first : PV_RunJoin_CircleRawMap52.fallback 0#usize=
    PV_RunJoin_CircleFallbackPrograms54.fallback 0#usize := by
  have hcanon : QC (PV_RunJoin_CircleRawTower52.field.CM31.ZERO,PV_RunJoin_CircleRawTower52.field.CM31.ONE) := ⟨czero,cone⟩
  have hmap := PV_RunJoin_CircleMapCanonical54.complete _ hcanon
  unfold PV_RunJoin_CircleRawMap52.fallback PV_RunJoin_CircleFallbackPrograms54.fallback
  have hrem : (0#usize%2#usize)=ok 0#usize := rfl
  have hidx : Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK 0#usize=
      ok (PV_RunJoin_CircleRawTower52.field.CM31.ZERO,PV_RunJoin_CircleRawTower52.field.CM31.ONE) := rfl
  simp only [hrem,hidx,bind_tc_ok,hmap]
  rfl

theorem second : PV_RunJoin_CircleRawMap52.fallback 1#usize=
    PV_RunJoin_CircleFallbackPrograms54.fallback 1#usize := by
  have hcanon : QC (PV_RunJoin_CircleRawTower52.field.CM31.ONE,PV_RunJoin_CircleRawTower52.field.CM31.ONE) := ⟨cone,cone⟩
  have hmap := PV_RunJoin_CircleMapCanonical54.complete _ hcanon
  unfold PV_RunJoin_CircleRawMap52.fallback PV_RunJoin_CircleFallbackPrograms54.fallback
  have hrem : (1#usize%2#usize)=ok 1#usize := rfl
  have hidx : Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK 1#usize=
      ok (PV_RunJoin_CircleRawTower52.field.CM31.ONE,PV_RunJoin_CircleRawTower52.field.CM31.ONE) := rfl
  simp only [hrem,hidx,bind_tc_ok,hmap]
  rfl
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleFallbackCompare54
