import JGu_Scratch0
import JGu_Level0_00
import JGk_TX2_ScratchIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Initial0
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem idx01 (s : reference.Scratch) :
    (JGu_Scratch0.s01 s).idx.val.take 1=[65593#u32] := by
  change ((JGu_Scratch0.s00 s).idx.set (JGu_Scratch0.s00 s).n (65593#u32)).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s00 s).idx.val.set 0 (65593#u32)).take (0+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s00 s).idx.val.length=16 := (JGu_Scratch0.s00 s).idx.property
    omega)]
  rfl
#print axioms idx01
theorem idx02 (s : reference.Scratch) :
    (JGu_Scratch0.s02 s).idx.val.take 2=[65593#u32,93499#u32] := by
  change ((JGu_Scratch0.s01 s).idx.set (JGu_Scratch0.s01 s).n (93499#u32)).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s01 s).idx.val.set 1 (93499#u32)).take (1+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s01 s).idx.val.length=16 := (JGu_Scratch0.s01 s).idx.property
    omega)]
  rw [idx01]
  rfl
#print axioms idx02
theorem idx03 (s : reference.Scratch) :
    (JGu_Scratch0.s03 s).idx.val.take 3=[65593#u32,93499#u32,147529#u32] := by
  change ((JGu_Scratch0.s02 s).idx.set (JGu_Scratch0.s02 s).n (147529#u32)).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s02 s).idx.val.set 2 (147529#u32)).take (2+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s02 s).idx.val.length=16 := (JGu_Scratch0.s02 s).idx.property
    omega)]
  rw [idx02]
  rfl
#print axioms idx03
theorem idx04 (s : reference.Scratch) :
    (JGu_Scratch0.s04 s).idx.val.take 4=[65593#u32,93499#u32,147529#u32,159813#u32] := by
  change ((JGu_Scratch0.s03 s).idx.set (JGu_Scratch0.s03 s).n (159813#u32)).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s03 s).idx.val.set 3 (159813#u32)).take (3+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s03 s).idx.val.length=16 := (JGu_Scratch0.s03 s).idx.property
    omega)]
  rw [idx03]
  rfl
#print axioms idx04
theorem idx05 (s : reference.Scratch) :
    (JGu_Scratch0.s05 s).idx.val.take 5=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32] := by
  change ((JGu_Scratch0.s04 s).idx.set (JGu_Scratch0.s04 s).n (183859#u32)).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s04 s).idx.val.set 4 (183859#u32)).take (4+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s04 s).idx.val.length=16 := (JGu_Scratch0.s04 s).idx.property
    omega)]
  rw [idx04]
  rfl
#print axioms idx05
theorem idx06 (s : reference.Scratch) :
    (JGu_Scratch0.s06 s).idx.val.take 6=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32] := by
  change ((JGu_Scratch0.s05 s).idx.set (JGu_Scratch0.s05 s).n (192317#u32)).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s05 s).idx.val.set 5 (192317#u32)).take (5+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s05 s).idx.val.length=16 := (JGu_Scratch0.s05 s).idx.property
    omega)]
  rw [idx05]
  rfl
#print axioms idx06
theorem idx07 (s : reference.Scratch) :
    (JGu_Scratch0.s07 s).idx.val.take 7=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32] := by
  change ((JGu_Scratch0.s06 s).idx.set (JGu_Scratch0.s06 s).n (193093#u32)).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s06 s).idx.val.set 6 (193093#u32)).take (6+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s06 s).idx.val.length=16 := (JGu_Scratch0.s06 s).idx.property
    omega)]
  rw [idx06]
  rfl
#print axioms idx07
theorem idx08 (s : reference.Scratch) :
    (JGu_Scratch0.s08 s).idx.val.take 8=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32] := by
  change ((JGu_Scratch0.s07 s).idx.set (JGu_Scratch0.s07 s).n (209371#u32)).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s07 s).idx.val.set 7 (209371#u32)).take (7+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s07 s).idx.val.length=16 := (JGu_Scratch0.s07 s).idx.property
    omega)]
  rw [idx07]
  rfl
#print axioms idx08
theorem idx09 (s : reference.Scratch) :
    (JGu_Scratch0.s09 s).idx.val.take 9=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32] := by
  change ((JGu_Scratch0.s08 s).idx.set (JGu_Scratch0.s08 s).n (216823#u32)).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s08 s).idx.val.set 8 (216823#u32)).take (8+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s08 s).idx.val.length=16 := (JGu_Scratch0.s08 s).idx.property
    omega)]
  rw [idx08]
  rfl
#print axioms idx09
theorem idx10 (s : reference.Scratch) :
    (JGu_Scratch0.s10 s).idx.val.take 10=[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32] := by
  change ((JGu_Scratch0.s09 s).idx.set (JGu_Scratch0.s09 s).n (245899#u32)).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s09 s).idx.val.set 9 (245899#u32)).take (9+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s09 s).idx.val.length=16 := (JGu_Scratch0.s09 s).idx.property
    omega)]
  rw [idx09]
  rfl
#print axioms idx10
theorem val01 (s : reference.Scratch) :
    (JGu_Scratch0.s01 s).val.val.take 1=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩)] := by
  change ((JGu_Scratch0.s00 s).val.set (JGu_Scratch0.s00 s).n (encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩))).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s00 s).val.val.set 0 (encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩))).take (0+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s00 s).val.val.length=16 := (JGu_Scratch0.s00 s).val.property
    omega)]
  rfl
#print axioms val01
theorem val02 (s : reference.Scratch) :
    (JGu_Scratch0.s02 s).val.val.take 2=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩)] := by
  change ((JGu_Scratch0.s01 s).val.set (JGu_Scratch0.s01 s).n (encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩))).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s01 s).val.val.set 1 (encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩))).take (1+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s01 s).val.val.length=16 := (JGu_Scratch0.s01 s).val.property
    omega)]
  rw [val01]
  rfl
#print axioms val02
theorem val03 (s : reference.Scratch) :
    (JGu_Scratch0.s03 s).val.val.take 3=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩)] := by
  change ((JGu_Scratch0.s02 s).val.set (JGu_Scratch0.s02 s).n (encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩))).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s02 s).val.val.set 2 (encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩))).take (2+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s02 s).val.val.length=16 := (JGu_Scratch0.s02 s).val.property
    omega)]
  rw [val02]
  rfl
#print axioms val03
theorem val04 (s : reference.Scratch) :
    (JGu_Scratch0.s04 s).val.val.take 4=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩)] := by
  change ((JGu_Scratch0.s03 s).val.set (JGu_Scratch0.s03 s).n (encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩))).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s03 s).val.val.set 3 (encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩))).take (3+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s03 s).val.val.length=16 := (JGu_Scratch0.s03 s).val.property
    omega)]
  rw [val03]
  rfl
#print axioms val04
theorem val05 (s : reference.Scratch) :
    (JGu_Scratch0.s05 s).val.val.take 5=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩)] := by
  change ((JGu_Scratch0.s04 s).val.set (JGu_Scratch0.s04 s).n (encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩))).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s04 s).val.val.set 4 (encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩))).take (4+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s04 s).val.val.length=16 := (JGu_Scratch0.s04 s).val.property
    omega)]
  rw [val04]
  rfl
#print axioms val05
theorem val06 (s : reference.Scratch) :
    (JGu_Scratch0.s06 s).val.val.take 6=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩)] := by
  change ((JGu_Scratch0.s05 s).val.set (JGu_Scratch0.s05 s).n (encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩))).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s05 s).val.val.set 5 (encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩))).take (5+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s05 s).val.val.length=16 := (JGu_Scratch0.s05 s).val.property
    omega)]
  rw [val05]
  rfl
#print axioms val06
theorem val07 (s : reference.Scratch) :
    (JGu_Scratch0.s07 s).val.val.take 7=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩)] := by
  change ((JGu_Scratch0.s06 s).val.set (JGu_Scratch0.s06 s).n (encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩))).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s06 s).val.val.set 6 (encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩))).take (6+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s06 s).val.val.length=16 := (JGu_Scratch0.s06 s).val.property
    omega)]
  rw [val06]
  rfl
#print axioms val07
theorem val08 (s : reference.Scratch) :
    (JGu_Scratch0.s08 s).val.val.take 8=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩)] := by
  change ((JGu_Scratch0.s07 s).val.set (JGu_Scratch0.s07 s).n (encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩))).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s07 s).val.val.set 7 (encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩))).take (7+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s07 s).val.val.length=16 := (JGu_Scratch0.s07 s).val.property
    omega)]
  rw [val07]
  rfl
#print axioms val08
theorem val09 (s : reference.Scratch) :
    (JGu_Scratch0.s09 s).val.val.take 9=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩)] := by
  change ((JGu_Scratch0.s08 s).val.set (JGu_Scratch0.s08 s).n (encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩))).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s08 s).val.val.set 8 (encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩))).take (8+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s08 s).val.val.length=16 := (JGu_Scratch0.s08 s).val.property
    omega)]
  rw [val08]
  rfl
#print axioms val09
theorem val10 (s : reference.Scratch) :
    (JGu_Scratch0.s10 s).val.val.take 10=[encodeState (JGu_LeafIteration0.value ⟨6,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨0,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨1,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨9,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨7,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨5,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨8,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨4,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨2,by decide⟩),encodeState (JGu_LeafIteration0.value ⟨3,by decide⟩)] := by
  change ((JGu_Scratch0.s09 s).val.set (JGu_Scratch0.s09 s).n (encodeState (JGu_LeafIteration0.value ⟨3,by decide⟩))).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGu_Scratch0.s09 s).val.val.set 9 (encodeState (JGu_LeafIteration0.value ⟨3,by decide⟩))).take (9+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGu_Scratch0.s09 s).val.val.length=16 := (JGu_Scratch0.s09 s).val.property
    omega)]
  rw [val09]
  rfl
#print axioms val10
theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JGu_Scratch0.s10 s) JGu_Level0_00.indices00 JGu_Level0_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact idx10 s
  · exact val10 s
#print axioms source
end AspisR1.JGu_Initial0
end
