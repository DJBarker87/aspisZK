import R1Z.PV_RunJoin_CircleFallbackCompare54
import R1Z.PV_RunJoin_SamplerCanonical54
import R1Z.PV_RunJoin_CircleMapSource54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralComplete54

theorem complete (block : Array U8 32#usize) (row : Bool) :
    PV_RunJoin_CircleRawMap52.circle_owned block row=PV_RunJoin_CircleFallbackPrograms54.circle block row := by
  obtain ⟨parameter,hp,hc⟩ := PV_RunJoin_SamplerCanonical54.complete block
  have hmap := PV_RunJoin_CircleMapCanonical54.complete parameter hc
  unfold PV_RunJoin_CircleRawMap52.circle_owned PV_RunJoin_CircleFallbackPrograms54.circle
  simp only [hp,bind_tc_ok,hmap]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro result _
  cases result with
  | Ok p => rfl
  | Err e =>
    cases row
    · exact PV_RunJoin_CircleFallbackCompare54.first
    · exact PV_RunJoin_CircleFallbackCompare54.second
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralComplete54
