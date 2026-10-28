import NDO_JGk_TX2_Scratch0
import NDO_JGk_TX2_Scratch1
import NDO_JGk_TX2_Scratch2
set_option autoImplicit false
namespace AspisR1.JGk_TX2_ScratchIndices
open Aeneas Aeneas.Std

theorem snoc_set {α : Type} (xs : List α) (i : Nat) (x : α) (bound : i<xs.length) :
    (xs.set i x).take (i+1)=xs.take i++[x] := by
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_set] using bound),List.take_set]
  rw [List.set_eq_of_length_le (by simp only [List.length_take];omega)]
  simp only [List.getElem_set_self]
#print axioms snoc_set
theorem front0_01 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s01 s).idx.val.take 1=[14297#u32] := by
  change ((JGk_TX2_Scratch0.s00 s).idx.set (JGk_TX2_Scratch0.s00 s).n 14297#u32).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s00 s).idx.val.set 0 14297#u32).take (0+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s00 s).idx.val.length=16 := (JGk_TX2_Scratch0.s00 s).idx.property;omega)]
  rfl
#print axioms front0_01
theorem front0_02 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s02 s).idx.val.take 2=[14297#u32,21248#u32] := by
  change ((JGk_TX2_Scratch0.s01 s).idx.set (JGk_TX2_Scratch0.s01 s).n 21248#u32).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s01 s).idx.val.set 1 21248#u32).take (1+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s01 s).idx.val.length=16 := (JGk_TX2_Scratch0.s01 s).idx.property;omega)]
  rw [front0_01]
  rfl
#print axioms front0_02
theorem front0_03 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s03 s).idx.val.take 3=[14297#u32,21248#u32,42158#u32] := by
  change ((JGk_TX2_Scratch0.s02 s).idx.set (JGk_TX2_Scratch0.s02 s).n 42158#u32).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s02 s).idx.val.set 2 42158#u32).take (2+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s02 s).idx.val.length=16 := (JGk_TX2_Scratch0.s02 s).idx.property;omega)]
  rw [front0_02]
  rfl
#print axioms front0_03
theorem front0_04 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s04 s).idx.val.take 4=[14297#u32,21248#u32,42158#u32,55377#u32] := by
  change ((JGk_TX2_Scratch0.s03 s).idx.set (JGk_TX2_Scratch0.s03 s).n 55377#u32).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s03 s).idx.val.set 3 55377#u32).take (3+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s03 s).idx.val.length=16 := (JGk_TX2_Scratch0.s03 s).idx.property;omega)]
  rw [front0_03]
  rfl
#print axioms front0_04
theorem front0_05 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s05 s).idx.val.take 5=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32] := by
  change ((JGk_TX2_Scratch0.s04 s).idx.set (JGk_TX2_Scratch0.s04 s).n 63860#u32).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s04 s).idx.val.set 4 63860#u32).take (4+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s04 s).idx.val.length=16 := (JGk_TX2_Scratch0.s04 s).idx.property;omega)]
  rw [front0_04]
  rfl
#print axioms front0_05
theorem front0_06 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s06 s).idx.val.take 6=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32] := by
  change ((JGk_TX2_Scratch0.s05 s).idx.set (JGk_TX2_Scratch0.s05 s).n 132355#u32).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s05 s).idx.val.set 5 132355#u32).take (5+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s05 s).idx.val.length=16 := (JGk_TX2_Scratch0.s05 s).idx.property;omega)]
  rw [front0_05]
  rfl
#print axioms front0_06
theorem front0_07 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s07 s).idx.val.take 7=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32] := by
  change ((JGk_TX2_Scratch0.s06 s).idx.set (JGk_TX2_Scratch0.s06 s).n 149624#u32).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s06 s).idx.val.set 6 149624#u32).take (6+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s06 s).idx.val.length=16 := (JGk_TX2_Scratch0.s06 s).idx.property;omega)]
  rw [front0_06]
  rfl
#print axioms front0_07
theorem front0_08 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s08 s).idx.val.take 8=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32] := by
  change ((JGk_TX2_Scratch0.s07 s).idx.set (JGk_TX2_Scratch0.s07 s).n 166165#u32).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s07 s).idx.val.set 7 166165#u32).take (7+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s07 s).idx.val.length=16 := (JGk_TX2_Scratch0.s07 s).idx.property;omega)]
  rw [front0_07]
  rfl
#print axioms front0_08
theorem front0_09 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s09 s).idx.val.take 9=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32] := by
  change ((JGk_TX2_Scratch0.s08 s).idx.set (JGk_TX2_Scratch0.s08 s).n 178080#u32).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s08 s).idx.val.set 8 178080#u32).take (8+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s08 s).idx.val.length=16 := (JGk_TX2_Scratch0.s08 s).idx.property;omega)]
  rw [front0_08]
  rfl
#print axioms front0_09
theorem front0_10 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s10 s).idx.val.take 10=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32] := by
  change ((JGk_TX2_Scratch0.s09 s).idx.set (JGk_TX2_Scratch0.s09 s).n 179622#u32).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s09 s).idx.val.set 9 179622#u32).take (9+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s09 s).idx.val.length=16 := (JGk_TX2_Scratch0.s09 s).idx.property;omega)]
  rw [front0_09]
  rfl
#print axioms front0_10
theorem front0_11 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s11 s).idx.val.take 11=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32] := by
  change ((JGk_TX2_Scratch0.s10 s).idx.set (JGk_TX2_Scratch0.s10 s).n 185637#u32).val.take 11=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s10 s).idx.val.set 10 185637#u32).take (10+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s10 s).idx.val.length=16 := (JGk_TX2_Scratch0.s10 s).idx.property;omega)]
  rw [front0_10]
  rfl
#print axioms front0_11
theorem front0_12 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch0.s12 s).idx.val.take 12=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32] := by
  change ((JGk_TX2_Scratch0.s11 s).idx.set (JGk_TX2_Scratch0.s11 s).n 218094#u32).val.take 12=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s11 s).idx.val.set 11 218094#u32).take (11+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch0.s11 s).idx.val.length=16 := (JGk_TX2_Scratch0.s11 s).idx.property;omega)]
  rw [front0_11]
  rfl
#print axioms front0_12
theorem front1_01 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s01 s).idx.val.take 1=[14297#u32] := by
  change ((JGk_TX2_Scratch1.s00 s).idx.set (JGk_TX2_Scratch1.s00 s).n 14297#u32).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s00 s).idx.val.set 0 14297#u32).take (0+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s00 s).idx.val.length=16 := (JGk_TX2_Scratch1.s00 s).idx.property;omega)]
  rfl
#print axioms front1_01
theorem front1_02 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s02 s).idx.val.take 2=[14297#u32,21248#u32] := by
  change ((JGk_TX2_Scratch1.s01 s).idx.set (JGk_TX2_Scratch1.s01 s).n 21248#u32).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s01 s).idx.val.set 1 21248#u32).take (1+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s01 s).idx.val.length=16 := (JGk_TX2_Scratch1.s01 s).idx.property;omega)]
  rw [front1_01]
  rfl
#print axioms front1_02
theorem front1_03 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s03 s).idx.val.take 3=[14297#u32,21248#u32,42158#u32] := by
  change ((JGk_TX2_Scratch1.s02 s).idx.set (JGk_TX2_Scratch1.s02 s).n 42158#u32).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s02 s).idx.val.set 2 42158#u32).take (2+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s02 s).idx.val.length=16 := (JGk_TX2_Scratch1.s02 s).idx.property;omega)]
  rw [front1_02]
  rfl
#print axioms front1_03
theorem front1_04 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s04 s).idx.val.take 4=[14297#u32,21248#u32,42158#u32,55377#u32] := by
  change ((JGk_TX2_Scratch1.s03 s).idx.set (JGk_TX2_Scratch1.s03 s).n 55377#u32).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s03 s).idx.val.set 3 55377#u32).take (3+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s03 s).idx.val.length=16 := (JGk_TX2_Scratch1.s03 s).idx.property;omega)]
  rw [front1_03]
  rfl
#print axioms front1_04
theorem front1_05 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s05 s).idx.val.take 5=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32] := by
  change ((JGk_TX2_Scratch1.s04 s).idx.set (JGk_TX2_Scratch1.s04 s).n 63860#u32).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s04 s).idx.val.set 4 63860#u32).take (4+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s04 s).idx.val.length=16 := (JGk_TX2_Scratch1.s04 s).idx.property;omega)]
  rw [front1_04]
  rfl
#print axioms front1_05
theorem front1_06 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s06 s).idx.val.take 6=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32] := by
  change ((JGk_TX2_Scratch1.s05 s).idx.set (JGk_TX2_Scratch1.s05 s).n 132355#u32).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s05 s).idx.val.set 5 132355#u32).take (5+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s05 s).idx.val.length=16 := (JGk_TX2_Scratch1.s05 s).idx.property;omega)]
  rw [front1_05]
  rfl
#print axioms front1_06
theorem front1_07 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s07 s).idx.val.take 7=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32] := by
  change ((JGk_TX2_Scratch1.s06 s).idx.set (JGk_TX2_Scratch1.s06 s).n 149624#u32).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s06 s).idx.val.set 6 149624#u32).take (6+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s06 s).idx.val.length=16 := (JGk_TX2_Scratch1.s06 s).idx.property;omega)]
  rw [front1_06]
  rfl
#print axioms front1_07
theorem front1_08 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s08 s).idx.val.take 8=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32] := by
  change ((JGk_TX2_Scratch1.s07 s).idx.set (JGk_TX2_Scratch1.s07 s).n 166165#u32).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s07 s).idx.val.set 7 166165#u32).take (7+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s07 s).idx.val.length=16 := (JGk_TX2_Scratch1.s07 s).idx.property;omega)]
  rw [front1_07]
  rfl
#print axioms front1_08
theorem front1_09 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s09 s).idx.val.take 9=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32] := by
  change ((JGk_TX2_Scratch1.s08 s).idx.set (JGk_TX2_Scratch1.s08 s).n 178080#u32).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s08 s).idx.val.set 8 178080#u32).take (8+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s08 s).idx.val.length=16 := (JGk_TX2_Scratch1.s08 s).idx.property;omega)]
  rw [front1_08]
  rfl
#print axioms front1_09
theorem front1_10 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s10 s).idx.val.take 10=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32] := by
  change ((JGk_TX2_Scratch1.s09 s).idx.set (JGk_TX2_Scratch1.s09 s).n 179622#u32).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s09 s).idx.val.set 9 179622#u32).take (9+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s09 s).idx.val.length=16 := (JGk_TX2_Scratch1.s09 s).idx.property;omega)]
  rw [front1_09]
  rfl
#print axioms front1_10
theorem front1_11 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s11 s).idx.val.take 11=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32] := by
  change ((JGk_TX2_Scratch1.s10 s).idx.set (JGk_TX2_Scratch1.s10 s).n 185637#u32).val.take 11=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s10 s).idx.val.set 10 185637#u32).take (10+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s10 s).idx.val.length=16 := (JGk_TX2_Scratch1.s10 s).idx.property;omega)]
  rw [front1_10]
  rfl
#print axioms front1_11
theorem front1_12 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch1.s12 s).idx.val.take 12=[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32] := by
  change ((JGk_TX2_Scratch1.s11 s).idx.set (JGk_TX2_Scratch1.s11 s).n 218094#u32).val.take 12=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s11 s).idx.val.set 11 218094#u32).take (11+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch1.s11 s).idx.val.length=16 := (JGk_TX2_Scratch1.s11 s).idx.property;omega)]
  rw [front1_11]
  rfl
#print axioms front1_12
theorem front2_01 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s01 s).idx.val.take 1=[3574#u32] := by
  change ((JGk_TX2_Scratch2.s00 s).idx.set (JGk_TX2_Scratch2.s00 s).n 3574#u32).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s00 s).idx.val.set 0 3574#u32).take (0+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s00 s).idx.val.length=16 := (JGk_TX2_Scratch2.s00 s).idx.property;omega)]
  rfl
#print axioms front2_01
theorem front2_02 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s02 s).idx.val.take 2=[3574#u32,5312#u32] := by
  change ((JGk_TX2_Scratch2.s01 s).idx.set (JGk_TX2_Scratch2.s01 s).n 5312#u32).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s01 s).idx.val.set 1 5312#u32).take (1+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s01 s).idx.val.length=16 := (JGk_TX2_Scratch2.s01 s).idx.property;omega)]
  rw [front2_01]
  rfl
#print axioms front2_02
theorem front2_03 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s03 s).idx.val.take 3=[3574#u32,5312#u32,10539#u32] := by
  change ((JGk_TX2_Scratch2.s02 s).idx.set (JGk_TX2_Scratch2.s02 s).n 10539#u32).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s02 s).idx.val.set 2 10539#u32).take (2+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s02 s).idx.val.length=16 := (JGk_TX2_Scratch2.s02 s).idx.property;omega)]
  rw [front2_02]
  rfl
#print axioms front2_03
theorem front2_04 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s04 s).idx.val.take 4=[3574#u32,5312#u32,10539#u32,13844#u32] := by
  change ((JGk_TX2_Scratch2.s03 s).idx.set (JGk_TX2_Scratch2.s03 s).n 13844#u32).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s03 s).idx.val.set 3 13844#u32).take (3+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s03 s).idx.val.length=16 := (JGk_TX2_Scratch2.s03 s).idx.property;omega)]
  rw [front2_03]
  rfl
#print axioms front2_04
theorem front2_05 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s05 s).idx.val.take 5=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32] := by
  change ((JGk_TX2_Scratch2.s04 s).idx.set (JGk_TX2_Scratch2.s04 s).n 15965#u32).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s04 s).idx.val.set 4 15965#u32).take (4+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s04 s).idx.val.length=16 := (JGk_TX2_Scratch2.s04 s).idx.property;omega)]
  rw [front2_04]
  rfl
#print axioms front2_05
theorem front2_06 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s06 s).idx.val.take 6=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32] := by
  change ((JGk_TX2_Scratch2.s05 s).idx.set (JGk_TX2_Scratch2.s05 s).n 33088#u32).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s05 s).idx.val.set 5 33088#u32).take (5+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s05 s).idx.val.length=16 := (JGk_TX2_Scratch2.s05 s).idx.property;omega)]
  rw [front2_05]
  rfl
#print axioms front2_06
theorem front2_07 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s07 s).idx.val.take 7=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32] := by
  change ((JGk_TX2_Scratch2.s06 s).idx.set (JGk_TX2_Scratch2.s06 s).n 37406#u32).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s06 s).idx.val.set 6 37406#u32).take (6+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s06 s).idx.val.length=16 := (JGk_TX2_Scratch2.s06 s).idx.property;omega)]
  rw [front2_06]
  rfl
#print axioms front2_07
theorem front2_08 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s08 s).idx.val.take 8=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32] := by
  change ((JGk_TX2_Scratch2.s07 s).idx.set (JGk_TX2_Scratch2.s07 s).n 41541#u32).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s07 s).idx.val.set 7 41541#u32).take (7+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s07 s).idx.val.length=16 := (JGk_TX2_Scratch2.s07 s).idx.property;omega)]
  rw [front2_07]
  rfl
#print axioms front2_08
theorem front2_09 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s09 s).idx.val.take 9=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32] := by
  change ((JGk_TX2_Scratch2.s08 s).idx.set (JGk_TX2_Scratch2.s08 s).n 44520#u32).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s08 s).idx.val.set 8 44520#u32).take (8+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s08 s).idx.val.length=16 := (JGk_TX2_Scratch2.s08 s).idx.property;omega)]
  rw [front2_08]
  rfl
#print axioms front2_09
theorem front2_10 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s10 s).idx.val.take 10=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32] := by
  change ((JGk_TX2_Scratch2.s09 s).idx.set (JGk_TX2_Scratch2.s09 s).n 44905#u32).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s09 s).idx.val.set 9 44905#u32).take (9+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s09 s).idx.val.length=16 := (JGk_TX2_Scratch2.s09 s).idx.property;omega)]
  rw [front2_09]
  rfl
#print axioms front2_10
theorem front2_11 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s11 s).idx.val.take 11=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32] := by
  change ((JGk_TX2_Scratch2.s10 s).idx.set (JGk_TX2_Scratch2.s10 s).n 46409#u32).val.take 11=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s10 s).idx.val.set 10 46409#u32).take (10+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s10 s).idx.val.length=16 := (JGk_TX2_Scratch2.s10 s).idx.property;omega)]
  rw [front2_10]
  rfl
#print axioms front2_11
theorem front2_12 (s : MultiproofConeRef.reference.Scratch) :
    (JGk_TX2_Scratch2.s12 s).idx.val.take 12=[3574#u32,5312#u32,10539#u32,13844#u32,15965#u32,33088#u32,37406#u32,41541#u32,44520#u32,44905#u32,46409#u32,54523#u32] := by
  change ((JGk_TX2_Scratch2.s11 s).idx.set (JGk_TX2_Scratch2.s11 s).n 54523#u32).val.take 12=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s11 s).idx.val.set 11 54523#u32).take (11+1)=_
  rw [snoc_set _ _ _ (by have e : (JGk_TX2_Scratch2.s11 s).idx.val.length=16 := (JGk_TX2_Scratch2.s11 s).idx.property;omega)]
  rw [front2_11]
  rfl
#print axioms front2_12
end AspisR1.JGk_TX2_ScratchIndices
