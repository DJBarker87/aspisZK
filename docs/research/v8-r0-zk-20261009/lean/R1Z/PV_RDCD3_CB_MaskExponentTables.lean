import R1Z.PV_RDCD3_CB_MaskIndices
import R1Z.PV_RDCD3_CB_OwnedMaskFill
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskExponentTables
open Aeneas Aeneas.Std Result

def widen {N : Usize} (exponents : Array U8 N) : Array Usize N :=
  ⟨exponents.val.map core.convert.num.FromUsizeU8.from,by simp only [List.length_map,exponents.property]⟩
theorem c1 : PV_RDCD3_CB_OwnedMaskFill.c1Exponents = widen PV_RDCD3_CB_MaskIndices.S.factors := by
  apply Subtype.ext
  simp only [PV_RDCD3_CB_OwnedMaskFill.c1Exponents,widen,PV_RDCD3_CB_MaskIndices.S.factors,
    PV_RDCD3_CB_MaskSource.state_only_hiding.FACTOR_EXPONENTS,Array.make,List.map_cons,List.map_nil,
    List.cons.injEq,and_true]
  repeat' constructor
  all_goals
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    decide
theorem mask : PV_RDCD3_CB_OwnedMaskFill.maskExponents = widen PV_RDCD3_CB_MaskIndices.S.maskFactors := by
  apply Subtype.ext
  simp only [PV_RDCD3_CB_OwnedMaskFill.maskExponents,widen,PV_RDCD3_CB_MaskIndices.S.maskFactors,
    PV_RDCD3_CB_MaskSource.state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS,Array.make,List.map_cons,List.map_nil,
    List.cons.injEq,and_true]
  repeat' constructor
  all_goals
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    decide
theorem read {N : Usize} (exponents : Array U8 N) (i : Usize) (inside : i.val<N.val) :
    Array.index_usize (widen exponents) i = (do
      let e ← Array.index_usize exponents i
      .ok (core.convert.num.FromUsizeU8.from e)) := by
  rw [PV_RDCD3_ArrayIndex.array_index_usize_ok exponents i inside,
    PV_RDCD3_ArrayIndex.array_index_usize_ok (widen exponents) i inside]
  simp only [widen,List.getElem_map,bind_tc_ok]
#print axioms c1
#print axioms mask
#print axioms read
end R1Z.PV_RDCD3_CB_MaskExponentTables
