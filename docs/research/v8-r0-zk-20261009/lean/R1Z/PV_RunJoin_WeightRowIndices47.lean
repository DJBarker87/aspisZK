import R1Z.PV_RunJoin_WeightRowCounters47
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRowIndices47
open Aeneas Aeneas.Std Result

theorem mul0 : Usize.wrapping_mul 2#usize 0#usize=0#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms mul0

theorem mul1 : Usize.wrapping_mul 2#usize 1#usize=2#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms mul1

theorem mul2 : Usize.wrapping_mul 2#usize 2#usize=4#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms mul2

theorem mul3 : Usize.wrapping_mul 2#usize 3#usize=6#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms mul3

theorem mul4 : Usize.wrapping_mul 2#usize 4#usize=8#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms mul4

theorem tau0 : Array.index_usize AspisR1ProducerRelease47.point_rows.TAU 0#usize=ok 3#usize := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms tau0

theorem coord9_0 : Usize.wrapping_sub 9#usize
    (Usize.wrapping_mul 2#usize 3#usize)=3#usize := by
  rw [mul3]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord9_0

theorem coord8_0 : Usize.wrapping_sub 8#usize
    (Usize.wrapping_mul 2#usize 3#usize)=2#usize := by
  rw [mul3]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord8_0

theorem tau1 : Array.index_usize AspisR1ProducerRelease47.point_rows.TAU 1#usize=ok 4#usize := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms tau1

theorem coord9_1 : Usize.wrapping_sub 9#usize
    (Usize.wrapping_mul 2#usize 4#usize)=1#usize := by
  rw [mul4]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord9_1

theorem coord8_1 : Usize.wrapping_sub 8#usize
    (Usize.wrapping_mul 2#usize 4#usize)=0#usize := by
  rw [mul4]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord8_1

theorem tau2 : Array.index_usize AspisR1ProducerRelease47.point_rows.TAU 2#usize=ok 2#usize := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms tau2

theorem coord9_2 : Usize.wrapping_sub 9#usize
    (Usize.wrapping_mul 2#usize 2#usize)=5#usize := by
  rw [mul2]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord9_2

theorem coord8_2 : Usize.wrapping_sub 8#usize
    (Usize.wrapping_mul 2#usize 2#usize)=4#usize := by
  rw [mul2]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord8_2

theorem tau3 : Array.index_usize AspisR1ProducerRelease47.point_rows.TAU 3#usize=ok 0#usize := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms tau3

theorem coord9_3 : Usize.wrapping_sub 9#usize
    (Usize.wrapping_mul 2#usize 0#usize)=9#usize := by
  rw [mul0]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord9_3

theorem coord8_3 : Usize.wrapping_sub 8#usize
    (Usize.wrapping_mul 2#usize 0#usize)=8#usize := by
  rw [mul0]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord8_3

theorem tau4 : Array.index_usize AspisR1ProducerRelease47.point_rows.TAU 4#usize=ok 1#usize := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms tau4

theorem coord9_4 : Usize.wrapping_sub 9#usize
    (Usize.wrapping_mul 2#usize 1#usize)=7#usize := by
  rw [mul1]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord9_4

theorem coord8_4 : Usize.wrapping_sub 8#usize
    (Usize.wrapping_mul 2#usize 1#usize)=6#usize := by
  rw [mul1]
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_WeightRowCounters47.sub_small _ _ (by scalar_tac)]
  scalar_tac
#print axioms coord8_4
end R1Z.PV_RunJoin_WeightRowIndices47
