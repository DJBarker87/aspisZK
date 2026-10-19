import CuSavingsGroups
import CuSavingsS2TableChunk0
import CuSavingsS2TableChunk1
import CuSavingsS2TableChunk2
import CuSavingsS2TableChunk3
import CuSavingsS2TableChunk4
import CuSavingsS2TableChunk5
import CuSavingsS2TableChunk6
import CuSavingsS2TableChunk7
import CuSavingsS2TableChunk8

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
theorem table_correct (j : Fin 64) (bit : Fin 16) :
    row (16*j.val+bit.val) < 1024 ∧
      groupMask (group j) bit = inactive (16*j.val+bit.val) := by
  fin_cases j
  · exact block_0 bit
  · exact block_1 bit
  · exact block_2 bit
  · exact block_3 bit
  · exact block_4 bit
  · exact block_5 bit
  · exact block_6 bit
  · exact block_7 bit
  · exact block_8 bit
  · exact block_9 bit
  · exact block_10 bit
  · exact block_11 bit
  · exact block_12 bit
  · exact block_13 bit
  · exact block_14 bit
  · exact block_15 bit
  · exact block_16 bit
  · exact block_17 bit
  · exact block_18 bit
  · exact block_19 bit
  · exact block_20 bit
  · exact block_21 bit
  · exact block_22 bit
  · exact block_23 bit
  · exact block_24 bit
  · exact block_25 bit
  · exact block_26 bit
  · exact block_27 bit
  · exact block_28 bit
  · exact block_29 bit
  · exact block_30 bit
  · exact block_31 bit
  · exact block_32 bit
  · exact block_33 bit
  · exact block_34 bit
  · exact block_35 bit
  · exact block_36 bit
  · exact block_37 bit
  · exact block_38 bit
  · exact block_39 bit
  · exact block_40 bit
  · exact block_41 bit
  · exact block_42 bit
  · exact block_43 bit
  · exact block_44 bit
  · exact block_45 bit
  · exact block_46 bit
  · exact block_47 bit
  · exact block_48 bit
  · exact block_49 bit
  · exact block_50 bit
  · exact block_51 bit
  · exact block_52 bit
  · exact block_53 bit
  · exact block_54 bit
  · exact block_55 bit
  · exact block_56 bit
  · exact block_57 bit
  · exact block_58 bit
  · exact block_59 bit
  · exact block_60 bit
  · exact block_61 bit
  · exact block_62 bit
  · exact block_63 bit

open scoped BigOperators
theorem grouped_inactive_eq {R : Type} [Semiring R]
    (coefficient : Fin 64 → R) (low : Fin 16 → R) :
    CuSavingsGroups.grouped group coefficient (fun g => CuSavingsGroups.maskWeight (groupMask g) low) =
      ∑ j, coefficient j * CuSavingsGroups.maskWeight (fun bit => inactive (16*j.val+bit.val)) low := by
  exact CuSavingsGroups.grouped_mask_eq group coefficient groupMask
    (fun j bit => inactive (16*j.val+bit.val)) low (fun j bit => (table_correct j bit).2)

#print axioms table_correct
#print axioms grouped_inactive_eq
end AspisR1.CuSavingsS2Tables
