import R1Z.PV_RunJoin_RecordPost43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroShapes43
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem cast_val {ty : UScalarTy} (x : UScalar ty) (tgt : UScalarTy) :
    (UScalar.cast tgt x).val = x.val % 2^tgt.numBits := by
  simp only [UScalar.cast,UScalar.val,BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]
#print axioms cast_val

theorem shape (ops : ExternalFuns) (i : Usize) (small : i.val<10) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops)
      (U8.wrapping_add 3#u8 (UScalar.cast .U8 i))=.ok (some (0#u8,0#usize)) := by
  have cases : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 ∨ i.val=8 ∨ i.val=9 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · have hi : i=0#usize := UScalar.eq_of_val_eq h0
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 0#usize)=3#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row3 ops
  · have hi : i=1#usize := UScalar.eq_of_val_eq h1
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 1#usize)=4#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row4 ops
  · have hi : i=2#usize := UScalar.eq_of_val_eq h2
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 2#usize)=5#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row5 ops
  · have hi : i=3#usize := UScalar.eq_of_val_eq h3
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 3#usize)=6#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row6 ops
  · have hi : i=4#usize := UScalar.eq_of_val_eq h4
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 4#usize)=7#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row7 ops
  · have hi : i=5#usize := UScalar.eq_of_val_eq h5
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 5#usize)=8#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row8 ops
  · have hi : i=6#usize := UScalar.eq_of_val_eq h6
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 6#usize)=9#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row9 ops
  · have hi : i=7#usize := UScalar.eq_of_val_eq h7
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 7#usize)=10#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row10 ops
  · have hi : i=8#usize := UScalar.eq_of_val_eq h8
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 8#usize)=11#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row11 ops
  · have hi : i=9#usize := UScalar.eq_of_val_eq h9
    subst i
    have hr : U8.wrapping_add 3#u8 (UScalar.cast .U8 9#usize)=12#u8 := by
      apply UScalar.eq_of_val_eq
      rw [U8.wrapping_add_val_eq,cast_val,UScalar.size_def]
      decide
    rw [hr]
    exact PV_RunJoin_RowShapes41.row12 ops
#print axioms shape
end R1Z.PV_RunJoin_ZeroShapes43
