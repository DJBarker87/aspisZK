import PV_B3_MaskSparseCopy
import R1Z.PV_Op134_Masks
import PV_B3_MaskSparseValues0
import PV_B3_MaskSparseValues1
import PV_B3_MaskSparseValues2
import PV_B3_MaskSparseValues3
import PV_B3_MaskSparseValues4
import PV_B3_MaskSparseValues5
import PV_B3_MaskSparseValues6
import PV_B3_MaskSparseValues7
namespace PV_B3_MaskRowExpected
open Aeneas Aeneas.Std Result PV_B3_Forest_134 PV_B3_MaskSparseStates
set_option autoImplicit false

theorem masks : PV_B3_SparseArray.array 64#usize M136 = R1Z.PV_Op134_Masks.masks := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [PV_B3_SparseArray.array, List.length_ofFn, R1Z.PV_Op134_Masks.length,
      show (64#usize).val = 64 from rfl]
  · intro k hk1 hk2
    have hk : k < 64 := by
      simpa only [PV_B3_SparseArray.array, List.length_ofFn,
        show (64#usize).val = 64 from rfl] using hk1
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 ∨ k = 40 ∨ k = 41 ∨ k = 42 ∨ k = 43 ∨ k = 44 ∨ k = 45 ∨ k = 46 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52 ∨ k = 53 ∨ k = 54 ∨ k = 55 ∨ k = 56 ∨ k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62 ∨ k = 63 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change M136 0 = 6144#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell00
    · change M136 1 = 6144#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell01
    · change M136 2 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell02
    · change M136 3 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell03
    · change M136 4 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell04
    · change M136 5 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell05
    · change M136 6 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell06
    · change M136 7 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues0.cell07
    · change M136 8 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell08
    · change M136 9 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell09
    · change M136 10 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell10
    · change M136 11 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell11
    · change M136 12 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell12
    · change M136 13 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell13
    · change M136 14 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell14
    · change M136 15 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues1.cell15
    · change M136 16 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell16
    · change M136 17 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell17
    · change M136 18 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell18
    · change M136 19 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell19
    · change M136 20 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell20
    · change M136 21 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell21
    · change M136 22 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell22
    · change M136 23 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues2.cell23
    · change M136 24 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell24
    · change M136 25 = 6144#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell25
    · change M136 26 = 4097#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell26
    · change M136 27 = 2048#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell27
    · change M136 28 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell28
    · change M136 29 = 2049#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell29
    · change M136 30 = 2048#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell30
    · change M136 31 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues3.cell31
    · change M136 32 = 2049#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell32
    · change M136 33 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell33
    · change M136 34 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell34
    · change M136 35 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell35
    · change M136 36 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell36
    · change M136 37 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell37
    · change M136 38 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell38
    · change M136 39 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues4.cell39
    · change M136 40 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell40
    · change M136 41 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell41
    · change M136 42 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell42
    · change M136 43 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell43
    · change M136 44 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell44
    · change M136 45 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell45
    · change M136 46 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell46
    · change M136 47 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues5.cell47
    · change M136 48 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell48
    · change M136 49 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell49
    · change M136 50 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell50
    · change M136 51 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell51
    · change M136 52 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell52
    · change M136 53 = 4097#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell53
    · change M136 54 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell54
    · change M136 55 = 6145#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues6.cell55
    · change M136 56 = 4097#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell56
    · change M136 57 = 26214#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell57
    · change M136 58 = 26214#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell58
    · change M136 59 = 26214#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell59
    · change M136 60 = 26214#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell60
    · change M136 61 = 26214#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell61
    · change M136 62 = 26214#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell62
    · change M136 63 = 1749#u16
      exact UScalar.eq_of_val_eq PV_B3_MaskSparseValues7.cell63

theorem op134_value : host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
    ok (.Ok R1Z.PV_Op134_Masks.masks) := by
  rw [PV_B3_MaskSparseCopy.source_result, masks]

theorem nonvacuity : ∃ m : Array U16 64#usize,
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 = ok (.Ok m) ∧
      m.val.length = 64 :=
  ⟨R1Z.PV_Op134_Masks.masks, op134_value, R1Z.PV_Op134_Masks.length⟩

#print axioms masks
#print axioms op134_value
#print axioms nonvacuity
end PV_B3_MaskRowExpected
