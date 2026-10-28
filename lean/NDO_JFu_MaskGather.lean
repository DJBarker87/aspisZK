import NDO_JFu_MaskInputs
import RPz7_FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskGather
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open JFu_ClaimsData JFu_MaskInputs
theorem call16_00 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 0#usize=ok (q000,claims) := by
  rfl

#print axioms call16_00
theorem call16_01 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 1#usize=ok (q001,claims) := by
  rfl

#print axioms call16_01
theorem call16_02 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 2#usize=ok (q002,claims) := by
  rfl

#print axioms call16_02
theorem call16_03 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 3#usize=ok (q003,claims) := by
  rfl

#print axioms call16_03
theorem call16_04 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 4#usize=ok (q004,claims) := by
  rfl

#print axioms call16_04
theorem call16_05 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 5#usize=ok (q005,claims) := by
  rfl

#print axioms call16_05
theorem call16_06 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 6#usize=ok (q006,claims) := by
  rfl

#print axioms call16_06
theorem call16_07 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 7#usize=ok (q007,claims) := by
  rfl

#print axioms call16_07
theorem call16_08 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 8#usize=ok (q008,claims) := by
  rfl

#print axioms call16_08
theorem call16_09 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 9#usize=ok (q009,claims) := by
  rfl

#print axioms call16_09
theorem call16_10 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 10#usize=ok (q010,claims) := by
  rfl

#print axioms call16_10
theorem call16_11 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 11#usize=ok (q011,claims) := by
  rfl

#print axioms call16_11
theorem call16_12 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 12#usize=ok (q012,claims) := by
  rfl

#print axioms call16_12
theorem call16_13 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 13#usize=ok (q013,claims) := by
  rfl

#print axioms call16_13
theorem call16_14 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 14#usize=ok (q014,claims) := by
  rfl

#print axioms call16_14
theorem call16_15 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn6 D claims 15#usize=ok (q015,claims) := by
  rfl

#print axioms call16_15
theorem indices16 : OraclePortStdBuilder.indices 16#usize=[0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] := rfl
#print axioms indices16
theorem gather16 {H : Type} (D : aspis_core.Digest32 H) :
    OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) claims=ok c1 := by
  unfold OraclePortStdBuilder.fromFn
  rw [indices16]
  simp only [FinishModel.closureFn9,FinishModel.closureFn5,OraclePortStdBuilder.fromFnLoop,call16_00,call16_01,call16_02,call16_03,call16_04,call16_05,call16_06,call16_07,call16_08,call16_09,call16_10,call16_11,call16_12,call16_13,call16_14,call16_15,bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms gather16
theorem call10_00 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 0#usize=ok (q016,claims) := by
  have plus : (16#usize+0#usize : Result Usize)=ok 16#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=0#usize) (by scalar_tac))
    have same : v=16#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_00
theorem call10_01 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 1#usize=ok (q017,claims) := by
  have plus : (16#usize+1#usize : Result Usize)=ok 17#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=1#usize) (by scalar_tac))
    have same : v=17#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_01
theorem call10_02 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 2#usize=ok (q018,claims) := by
  have plus : (16#usize+2#usize : Result Usize)=ok 18#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=2#usize) (by scalar_tac))
    have same : v=18#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_02
theorem call10_03 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 3#usize=ok (q019,claims) := by
  have plus : (16#usize+3#usize : Result Usize)=ok 19#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=3#usize) (by scalar_tac))
    have same : v=19#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_03
theorem call10_04 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 4#usize=ok (q020,claims) := by
  have plus : (16#usize+4#usize : Result Usize)=ok 20#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=4#usize) (by scalar_tac))
    have same : v=20#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_04
theorem call10_05 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 5#usize=ok (q021,claims) := by
  have plus : (16#usize+5#usize : Result Usize)=ok 21#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=5#usize) (by scalar_tac))
    have same : v=21#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_05
theorem call10_06 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 6#usize=ok (q022,claims) := by
  have plus : (16#usize+6#usize : Result Usize)=ok 22#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=6#usize) (by scalar_tac))
    have same : v=22#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_06
theorem call10_07 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 7#usize=ok (q023,claims) := by
  have plus : (16#usize+7#usize : Result Usize)=ok 23#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=7#usize) (by scalar_tac))
    have same : v=23#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_07
theorem call10_08 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 8#usize=ok (q024,claims) := by
  have plus : (16#usize+8#usize : Result Usize)=ok 24#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=8#usize) (by scalar_tac))
    have same : v=24#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_08
theorem call10_09 {H : Type} (D : aspis_core.Digest32 H) :
    FinishModel.closureFn2 D claims 9#usize=ok (q025,claims) := by
  have plus : (16#usize+9#usize : Result Usize)=ok 25#usize := by
    obtain ⟨v,success,numeric⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=16#usize) (y:=9#usize) (by scalar_tac))
    have same : v=25#usize := by scalar_tac
    exact same ▸ success
  unfold FinishModel.closureFn2
  rw [plus,bind_tc_ok]
  rfl

#print axioms call10_09
theorem indices10 : OraclePortStdBuilder.indices 10#usize=[0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize] := rfl
#print axioms indices10
theorem gather10 {H : Type} (D : aspis_core.Digest32 H) :
    OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) claims=ok maskOnly := by
  unfold OraclePortStdBuilder.fromFn
  rw [indices10]
  simp only [FinishModel.closureFn9,FinishModel.closureFn5,OraclePortStdBuilder.fromFnLoop,call10_00,call10_01,call10_02,call10_03,call10_04,call10_05,call10_06,call10_07,call10_08,call10_09,bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms gather10
end AspisR1.JFu_MaskGather
end
