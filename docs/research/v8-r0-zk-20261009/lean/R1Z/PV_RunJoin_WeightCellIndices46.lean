import R1Z.PV_RunJoin_WeightCell46
import R1Z.PV_RunJoin_WeightCounters46
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCellIndices46
open Aeneas Aeneas.Std Result

theorem add4 : Usize.wrapping_add 4#usize 1#usize=5#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add4

theorem add5 : Usize.wrapping_add 5#usize 1#usize=6#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add5

theorem add6 : Usize.wrapping_add 6#usize 1#usize=7#usize := by
  apply UScalar.eq_of_val_eq
  rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
  scalar_tac
#print axioms add6

theorem index0 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 0#usize=ok a0 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index0

theorem index1 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 1#usize=ok a1 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index1

theorem index2 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 2#usize=ok a2 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index2

theorem index3 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 3#usize=ok a3 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index3

theorem index4 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 4#usize=ok a4 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index4

theorem index5 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 5#usize=ok a5 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index5

theorem index6 {A : Type} (a0 a1 a2 a3 a4 a5 a6 : A) :
    Array.index_usize (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6]) 6#usize=ok a6 := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]
  rfl
#print axioms index6
theorem zero : AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO=
    PV_RunJoin_WeightWide46.toWide PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ZERO := by
  unfold AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO
    AspisR1ProducerRelease47.field.QM31.ZERO
    PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ZERO
    PV_B2_251c1.aspis_core.field.QM31.ZERO
  rfl
#print axioms zero
end R1Z.PV_RunJoin_WeightCellIndices46
