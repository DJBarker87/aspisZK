import JFu_MaskInputs
import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskGather
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open JFu_ClaimsData JFu_MaskInputs
theorem call16_00 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 0#usize=ok (q000,claims) := rfl
#print axioms call16_00
theorem call16_01 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 1#usize=ok (q001,claims) := rfl
#print axioms call16_01
theorem call16_02 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 2#usize=ok (q002,claims) := rfl
#print axioms call16_02
theorem call16_03 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 3#usize=ok (q003,claims) := rfl
#print axioms call16_03
theorem call16_04 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 4#usize=ok (q004,claims) := rfl
#print axioms call16_04
theorem call16_05 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 5#usize=ok (q005,claims) := rfl
#print axioms call16_05
theorem call16_06 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 6#usize=ok (q006,claims) := rfl
#print axioms call16_06
theorem call16_07 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 7#usize=ok (q007,claims) := rfl
#print axioms call16_07
theorem call16_08 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 8#usize=ok (q008,claims) := rfl
#print axioms call16_08
theorem call16_09 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 9#usize=ok (q009,claims) := rfl
#print axioms call16_09
theorem call16_10 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 10#usize=ok (q010,claims) := rfl
#print axioms call16_10
theorem call16_11 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 11#usize=ok (q011,claims) := rfl
#print axioms call16_11
theorem call16_12 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 12#usize=ok (q012,claims) := rfl
#print axioms call16_12
theorem call16_13 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 13#usize=ok (q013,claims) := rfl
#print axioms call16_13
theorem call16_14 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 14#usize=ok (q014,claims) := rfl
#print axioms call16_14
theorem call16_15 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn9 D).call_mut claims 15#usize=ok (q015,claims) := rfl
#print axioms call16_15
theorem indices16 : OraclePortStdBuilder.indices 16#usize=[0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] := rfl
#print axioms indices16
theorem gather16 {H : Type} (D : aspis_core.Digest32 H) :
    OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) claims=ok c1 := by
  unfold OraclePortStdBuilder.fromFn
  rw [indices16]
  simp only [OraclePortStdBuilder.fromFnLoop,call16_00,call16_01,call16_02,call16_03,call16_04,call16_05,call16_06,call16_07,call16_08,call16_09,call16_10,call16_11,call16_12,call16_13,call16_14,call16_15,bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms gather16
theorem call10_00 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 0#usize=ok (q016,claims) := rfl
#print axioms call10_00
theorem call10_01 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 1#usize=ok (q017,claims) := rfl
#print axioms call10_01
theorem call10_02 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 2#usize=ok (q018,claims) := rfl
#print axioms call10_02
theorem call10_03 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 3#usize=ok (q019,claims) := rfl
#print axioms call10_03
theorem call10_04 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 4#usize=ok (q020,claims) := rfl
#print axioms call10_04
theorem call10_05 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 5#usize=ok (q021,claims) := rfl
#print axioms call10_05
theorem call10_06 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 6#usize=ok (q022,claims) := rfl
#print axioms call10_06
theorem call10_07 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 7#usize=ok (q023,claims) := rfl
#print axioms call10_07
theorem call10_08 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 8#usize=ok (q024,claims) := rfl
#print axioms call10_08
theorem call10_09 {H : Type} (D : aspis_core.Digest32 H) :
    (FinishModel.closureFn5 D).call_mut claims 9#usize=ok (q025,claims) := rfl
#print axioms call10_09
theorem indices10 : OraclePortStdBuilder.indices 10#usize=[0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize] := rfl
#print axioms indices10
theorem gather10 {H : Type} (D : aspis_core.Digest32 H) :
    OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) claims=ok maskOnly := by
  unfold OraclePortStdBuilder.fromFn
  rw [indices10]
  simp only [OraclePortStdBuilder.fromFnLoop,call10_00,call10_01,call10_02,call10_03,call10_04,call10_05,call10_06,call10_07,call10_08,call10_09,bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms gather10
end AspisR1.JFu_MaskGather
end
