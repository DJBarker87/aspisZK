import PV_B3P_PathStep15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def path_tail15_7 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31) (state : PathState15) : Result PathState15 := do
  let i35 ← lift (Std.Usize.wrapping_add 1#usize 7#usize)
  let current7 ← Array.index_usize openings.z i35
  let q54 ← aspis_core.field.QM31.mul path_selector minus
  let q55 ← Array.index_usize openings.succ_z 7#usize
  let q56 ← aspis_core.field.QM31.sub q55 current7
  let q57 ← aspis_core.field.QM31.mul q54 q56
  let i36 ← lift (Std.Usize.wrapping_add 1#usize 7#usize)
  let path16 ← Array.update state i36 q57
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
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.sub aspis_core.field.QM31.mul path_step15
theorem path_cell15_7 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31) (state : PathState15) (hsub : aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit = .ok minus) (hmul : aspis_core.field.QM31.mul path_selector bit = .ok right) :
    path_tail15_7 path_selector openings bit minus right state = (path_step15 path_selector openings bit state 7#usize >>= Result.ok) := by
  unfold path_tail15_7
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
  exact (PV_B3P_Binding9227.result_right _).symm
theorem path_fold15_7 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (bit minus right : aspis_core.field.QM31) (state : PathState15) (hsub : aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit = .ok minus) (hmul : aspis_core.field.QM31.mul path_selector bit = .ok right) :
    path_tail15_7 path_selector openings bit minus right state =
      PV_B3P_Ordered227.fold (path_step15 path_selector openings bit)
        [7#usize] state := by
  rw [path_cell15_7 path_selector openings bit minus right state hsub hmul]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  rfl
#print axioms path_cell15_7
#print axioms path_fold15_7
end PV_B3P_Native15227
