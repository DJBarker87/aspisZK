import R1Z.ProverCommitInactiveSource49
import R1Z.ProverCommitArrayIndex25
import R0Z.HonestView
/-! Literal 64-entry source table and the model copy-active table agree.
Only the small table is inspected; no 1024-row finite set is evaluated. -/
set_option autoImplicit false
namespace R1Z.ProverCommitInactiveTable49
open Aeneas Aeneas.Std Result AspisR1InactiveOwner49

def table (i : Fin 64) : U16 :=
  owned.MASKS.val[i.val]'(by rw [owned.MASKS.property];exact i.isLt)

theorem table_value_0 (i : Fin 16) :
    (table ⟨0+i.val,by have := i.isLt;omega⟩).val=
      R0P.copyActiveRowMasks ⟨0+i.val,by have := i.isLt;omega⟩ := by
  fin_cases i <;> simp only [table,owned.MASKS,R0P.copyActiveRowMasks,Array.make,
    Fin.cons_succ,Fin.cons_zero,List.getElem_cons_succ,List.getElem_cons_zero] <;> rfl

theorem table_value_1 (i : Fin 16) :
    (table ⟨16+i.val,by have := i.isLt;omega⟩).val=
      R0P.copyActiveRowMasks ⟨16+i.val,by have := i.isLt;omega⟩ := by
  fin_cases i <;> simp only [table,owned.MASKS,R0P.copyActiveRowMasks,Array.make,
    Fin.cons_succ,Fin.cons_zero,List.getElem_cons_succ,List.getElem_cons_zero] <;> rfl

theorem table_value_2 (i : Fin 16) :
    (table ⟨32+i.val,by have := i.isLt;omega⟩).val=
      R0P.copyActiveRowMasks ⟨32+i.val,by have := i.isLt;omega⟩ := by
  fin_cases i <;> simp only [table,owned.MASKS,R0P.copyActiveRowMasks,Array.make,
    Fin.cons_succ,Fin.cons_zero,List.getElem_cons_succ,List.getElem_cons_zero] <;> rfl

theorem table_value_3 (i : Fin 16) :
    (table ⟨48+i.val,by have := i.isLt;omega⟩).val=
      R0P.copyActiveRowMasks ⟨48+i.val,by have := i.isLt;omega⟩ := by
  fin_cases i <;> simp only [table,owned.MASKS,R0P.copyActiveRowMasks,Array.make,
    Fin.cons_succ,Fin.cons_zero,List.getElem_cons_succ,List.getElem_cons_zero] <;> rfl

theorem table_value (i : Fin 64) : (table i).val=R0P.copyActiveRowMasks i := by
  by_cases h0 : i.val<16
  · have he : i=(⟨0+i.val,by omega⟩ : Fin 64) := Fin.ext (by change i.val=0+i.val;omega)
    rw [he];exact table_value_0 ⟨i.val,h0⟩
  · by_cases h1 : i.val<32
    · have he : i=(⟨16+(i.val-16),by omega⟩ : Fin 64) := Fin.ext (by change i.val=16+(i.val-16);omega)
      rw [he];exact table_value_1 ⟨i.val-16,by omega⟩
    · by_cases h2 : i.val<48
      · have he : i=(⟨32+(i.val-32),by omega⟩ : Fin 64) := Fin.ext (by change i.val=32+(i.val-32);omega)
        rw [he];exact table_value_2 ⟨i.val-32,by omega⟩
      · have hi := i.isLt
        have he : i=(⟨48+(i.val-48),by omega⟩ : Fin 64) := Fin.ext (by change i.val=48+(i.val-48);omega)
        rw [he];exact table_value_3 ⟨i.val-48,by omega⟩

theorem table_index (i : Usize) (hi : i.val<64) :
    Array.index_usize owned.MASKS i=ok (table ⟨i.val,hi⟩) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ hi]
  rfl

theorem shift_mask (m : U16) (s : U32) (hs : s.val<16) :
    ((U16.wrapping_shr m s)&&&1#u16).val=(m.val/2^s.val)%2 := by
  change ((m.bv.ushiftRight (s.val%16))&&&(1#u16).bv).toNat=_
  simp only [BitVec.toNat_and]
  rw [Nat.mod_eq_of_lt hs]
  change (m.val >>> s.val)&&&1=_
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem zero_iff (m : U16) (s : U32) (hs : s.val<16) :
    ((U16.wrapping_shr m s)&&&1#u16)=0#u16 ↔ m.val.testBit s.val=false := by
  have he (v : U16) : v=0#u16 ↔ v.val=0 := by constructor <;> intro h <;> scalar_tac
  rw [he,shift_mask m s hs,Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]
  omega

#print axioms table_value_0
#print axioms table_value_1
#print axioms table_value_2
#print axioms table_value_3
#print axioms table_value
#print axioms table_index
#print axioms shift_mask
#print axioms zero_iff
end R1Z.ProverCommitInactiveTable49
