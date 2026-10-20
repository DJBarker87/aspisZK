import AspisR1QueryGeometryActual.Funs
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace R17ActualTableEntriesIndices

theorem a00_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[0+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00[j]? := by
  let pre := ([] : List (Std.U32 × Std.U32))
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 0 := by simp [pre]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [hpre]
  simp only [Nat.zero_add, Nat.sub_zero]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length]; exact hj)
#print axioms a00_entry_index

theorem a01_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[32+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 32 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 32+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length]; exact hj)
#print axioms a01_entry_index

theorem a02_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[64+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 64 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 64+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length]; exact hj)
#print axioms a02_entry_index

theorem a03_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[96+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 96 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 96+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length]; exact hj)
#print axioms a03_entry_index

theorem a04_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[128+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 128 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 128+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length]; exact hj)
#print axioms a04_entry_index

theorem a05_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[160+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 160 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 160+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length]; exact hj)
#print axioms a05_entry_index

theorem a06_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[192+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 192 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 192+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length]; exact hj)
#print axioms a06_entry_index

theorem a07_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[224+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 224 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 224+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length]; exact hj)
#print axioms a07_entry_index

theorem a08_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[256+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 256 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 256+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length]; exact hj)
#print axioms a08_entry_index

theorem a09_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[288+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 288 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 288+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length]; exact hj)
#print axioms a09_entry_index

theorem a10_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[320+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 320 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 320+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10_length]; exact hj)
#print axioms a10_entry_index

theorem a11_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[352+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 352 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 352+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11_length]; exact hj)
#print axioms a11_entry_index

theorem a12_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[384+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 384 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 384+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12_length]; exact hj)
#print axioms a12_entry_index

theorem a13_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[416+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 416 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 416+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13_length]; exact hj)
#print axioms a13_entry_index

theorem a14_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[448+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 448 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 448+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj)
#print axioms a14_entry_index

theorem a15_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[480+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14
  let suffix := ([] : List (Std.U32 × Std.U32))
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 480 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_11_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_12_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_13_length, AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 480+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_15_length]; exact hj)
#print axioms a15_entry_index

theorem b00_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[0+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00[j]? := by
  let pre := ([] : List (Std.U32 × Std.U32))
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 0 := by simp [pre]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [hpre]
  simp only [Nat.zero_add, Nat.sub_zero]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length]; exact hj)
#print axioms b00_entry_index

theorem b01_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[32+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 32 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 32+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length]; exact hj)
#print axioms b01_entry_index

theorem b02_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[64+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 64 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 64+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length]; exact hj)
#print axioms b02_entry_index

theorem b03_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[96+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 96 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 96+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length]; exact hj)
#print axioms b03_entry_index

theorem b04_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[128+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 128 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 128+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length]; exact hj)
#print axioms b04_entry_index

theorem b05_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[160+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 160 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 160+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length]; exact hj)
#print axioms b05_entry_index

theorem b06_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[192+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 192 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 192+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length]; exact hj)
#print axioms b06_entry_index

theorem b07_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[224+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 224 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 224+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length]; exact hj)
#print axioms b07_entry_index

theorem b08_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[256+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 256 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 256+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length]; exact hj)
#print axioms b08_entry_index

theorem b09_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[288+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 288 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 288+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length]; exact hj)
#print axioms b09_entry_index

theorem b10_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[320+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 320 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 320+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10_length]; exact hj)
#print axioms b10_entry_index

theorem b11_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[352+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 352 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 352+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11_length]; exact hj)
#print axioms b11_entry_index

theorem b12_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[384+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 384 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 384+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12_length]; exact hj)
#print axioms b12_entry_index

theorem b13_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[416+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 416 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 416+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13_length]; exact hj)
#print axioms b13_entry_index

theorem b14_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[448+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13
  let suffix := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 448 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 448+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14_length]; exact hj)
#print axioms b14_entry_index

theorem b15_entry_index (j : Nat) (hj : j < 32) :
    AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries[480+j]? = AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15[j]? := by
  let pre := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13 ++ AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14
  let suffix := ([] : List (Std.U32 × Std.U32))
  let tail := AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15 ++ suffix
  have hshape : AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries = pre ++ tail := by
    dsimp only [AspisR1QueryGeometryActual.fast_domain.TABLE_B_entries, pre, tail, suffix]
    simp only [List.append_assoc, List.nil_append, List.append_nil]
  have hpre : pre.length = 480 := by
    simp [pre, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_00_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_01_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_02_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_03_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_04_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_05_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_06_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_07_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_08_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_09_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_10_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_11_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_12_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_13_length, AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_14_length]
  rw [hshape]
  rw [List.getElem?_append_right (by rw [hpre]; omega)]
  rw [show 480+j-pre.length = j by rw [hpre]; omega]
  dsimp only [tail]
  exact List.getElem?_append_left (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_B_chunk_15_length]; exact hj)
#print axioms b15_entry_index

end R17ActualTableEntriesIndices
