import PV_B3P_PathCell15_3227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def path_tail15_2 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31) (state : PathState15) : Result PathState15 := do
  let i10 ← lift (Std.Usize.wrapping_add 1#usize 2#usize)
  let current2 ← Array.index_usize openings.z i10
  let q19 ← aspis_core.field.QM31.mul path_selector minus
  let q20 ← Array.index_usize openings.succ_z 2#usize
  let q21 ← aspis_core.field.QM31.sub q20 current2
  let q22 ← aspis_core.field.QM31.mul q19 q21
  let i11 ← lift (Std.Usize.wrapping_add 1#usize 2#usize)
  let path6 ← Array.update state i11 q22
  let i12 ←
    lift (Std.Usize.wrapping_add aspis_statement.poseidon2.RATE 2#usize)
  let q23 ← Array.index_usize openings.succ_z i12
  let q24 ← aspis_core.field.QM31.sub q23 current2
  let q25 ← aspis_core.field.QM31.mul right q24
  let i13 ←
    lift (Std.Usize.wrapping_add 1#usize
      aspis_statement.poseidon2.DIGEST_ELEMS)
  let i14 ← lift (Std.Usize.wrapping_add i13 2#usize)
  let path7 ← Array.update path6 i14 q25
  let i15 ← lift (Std.Usize.wrapping_add 1#usize 3#usize)
  let current3 ← Array.index_usize openings.z i15
  let q26 ← aspis_core.field.QM31.mul path_selector minus
  let q27 ← Array.index_usize openings.succ_z 3#usize
  let q28 ← aspis_core.field.QM31.sub q27 current3
  let q29 ← aspis_core.field.QM31.mul q26 q28
  let i16 ← lift (Std.Usize.wrapping_add 1#usize 3#usize)
  let path8 ← Array.update path7 i16 q29
  let i17 ←
    lift (Std.Usize.wrapping_add aspis_statement.poseidon2.RATE 3#usize)
  let q30 ← Array.index_usize openings.succ_z i17
  let q31 ← aspis_core.field.QM31.sub q30 current3
  let q32 ← aspis_core.field.QM31.mul right q31
  let i18 ←
    lift (Std.Usize.wrapping_add 1#usize
      aspis_statement.poseidon2.DIGEST_ELEMS)
  let i19 ← lift (Std.Usize.wrapping_add i18 3#usize)
  let path9 ← Array.update path8 i19 q32
  let i20 ← lift (Std.Usize.wrapping_add 1#usize 4#usize)
  let current4 ← Array.index_usize openings.z i20
  let q33 ← aspis_core.field.QM31.mul path_selector minus
  let q34 ← Array.index_usize openings.succ_z 4#usize
  let q35 ← aspis_core.field.QM31.sub q34 current4
  let q36 ← aspis_core.field.QM31.mul q33 q35
  let i21 ← lift (Std.Usize.wrapping_add 1#usize 4#usize)
  let path10 ← Array.update path9 i21 q36
  let i22 ←
    lift (Std.Usize.wrapping_add aspis_statement.poseidon2.RATE 4#usize)
  let q37 ← Array.index_usize openings.succ_z i22
  let q38 ← aspis_core.field.QM31.sub q37 current4
  let q39 ← aspis_core.field.QM31.mul right q38
  let i23 ←
    lift (Std.Usize.wrapping_add 1#usize
      aspis_statement.poseidon2.DIGEST_ELEMS)
  let i24 ← lift (Std.Usize.wrapping_add i23 4#usize)
  let path11 ← Array.update path10 i24 q39
  let i25 ← lift (Std.Usize.wrapping_add 1#usize 5#usize)
  let current5 ← Array.index_usize openings.z i25
  let q40 ← aspis_core.field.QM31.mul path_selector minus
  let q41 ← Array.index_usize openings.succ_z 5#usize
  let q42 ← aspis_core.field.QM31.sub q41 current5
  let q43 ← aspis_core.field.QM31.mul q40 q42
  let i26 ← lift (Std.Usize.wrapping_add 1#usize 5#usize)
  let path12 ← Array.update path11 i26 q43
  let i27 ←
    lift (Std.Usize.wrapping_add aspis_statement.poseidon2.RATE 5#usize)
  let q44 ← Array.index_usize openings.succ_z i27
  let q45 ← aspis_core.field.QM31.sub q44 current5
  let q46 ← aspis_core.field.QM31.mul right q45
  let i28 ←
    lift (Std.Usize.wrapping_add 1#usize
      aspis_statement.poseidon2.DIGEST_ELEMS)
  let i29 ← lift (Std.Usize.wrapping_add i28 5#usize)
  let path13 ← Array.update path12 i29 q46
  let i30 ← lift (Std.Usize.wrapping_add 1#usize 6#usize)
  let current6 ← Array.index_usize openings.z i30
  let q47 ← aspis_core.field.QM31.mul path_selector minus
  let q48 ← Array.index_usize openings.succ_z 6#usize
  let q49 ← aspis_core.field.QM31.sub q48 current6
  let q50 ← aspis_core.field.QM31.mul q47 q49
  let i31 ← lift (Std.Usize.wrapping_add 1#usize 6#usize)
  let path14 ← Array.update path13 i31 q50
  let i32 ←
    lift (Std.Usize.wrapping_add aspis_statement.poseidon2.RATE 6#usize)
  let q51 ← Array.index_usize openings.succ_z i32
  let q52 ← aspis_core.field.QM31.sub q51 current6
  let q53 ← aspis_core.field.QM31.mul right q52
  let i33 ←
    lift (Std.Usize.wrapping_add 1#usize
      aspis_statement.poseidon2.DIGEST_ELEMS)
  let i34 ← lift (Std.Usize.wrapping_add i33 6#usize)
  let path15 ← Array.update path14 i34 q53
  let i35 ← lift (Std.Usize.wrapping_add 1#usize 7#usize)
  let current7 ← Array.index_usize openings.z i35
  let q54 ← aspis_core.field.QM31.mul path_selector minus
  let q55 ← Array.index_usize openings.succ_z 7#usize
  let q56 ← aspis_core.field.QM31.sub q55 current7
  let q57 ← aspis_core.field.QM31.mul q54 q56
  let i36 ← lift (Std.Usize.wrapping_add 1#usize 7#usize)
  let path16 ← Array.update path15 i36 q57
  let i37 ←
    lift (Std.Usize.wrapping_add aspis_statement.poseidon2.RATE 7#usize)
  let q58 ← Array.index_usize openings.succ_z i37
  let q59 ← aspis_core.field.QM31.sub q58 current7
  let q60 ← aspis_core.field.QM31.mul right q59
  let i38 ←
    lift (Std.Usize.wrapping_add 1#usize
      aspis_statement.poseidon2.DIGEST_ELEMS)
  let i39 ← lift (Std.Usize.wrapping_add i38 7#usize)
  Array.update path16 i39 q60
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.sub aspis_core.field.QM31.mul path_step15 path_tail15_3
theorem path_cell15_2 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31) (state : PathState15) (hsub : aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit = .ok minus) (hmul : aspis_core.field.QM31.mul path_selector bit = .ok right) :
    path_tail15_2 path_selector openings bit minus right state = (path_step15 path_selector openings bit state 2#usize >>= path_tail15_3 path_selector openings bit minus right) := by
  unfold path_tail15_2
  conv_rhs => simp only [path_step15,PV_B3P_Ordered227.bind_assoc,lift,bind_tc_ok,hsub,hmul]
  simp only [lift,bind_tc_ok,hsub,hmul]
  apply bind_equal9
  intro v0
  apply bind_equal9
  intro v1
  apply bind_equal9
  intro v2
  apply bind_equal9
  intro v3
  apply bind_equal9
  intro v4
  apply bind_equal9
  intro v5
  apply bind_equal9
  intro v6
  apply bind_equal9
  intro v7
  apply bind_equal9
  intro v8
  apply bind_equal9
  intro v9
  unfold path_tail15_3
  rfl
theorem path_fold15_2 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31) (state : PathState15) (hsub : aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit = .ok minus) (hmul : aspis_core.field.QM31.mul path_selector bit = .ok right) :
    path_tail15_2 path_selector openings bit minus right state =
      PV_B3P_Ordered227.fold (path_step15 path_selector openings bit)
        [2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] state := by
  rw [path_cell15_2 path_selector openings bit minus right state hsub hmul]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  apply congrArg (fun k => path_step15 path_selector openings bit state 2#usize >>= k)
  funext next
  exact path_fold15_3 path_selector openings bit minus right next hsub hmul
#print axioms path_cell15_2
#print axioms path_fold15_2
end PV_B3P_Native15227
