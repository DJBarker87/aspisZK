import JHc_Tree2Part3
import JHc_Tree2Part4
import JGy_LightCore
import JHc_Tree2Part5
import JHc_Tree2Part6
import JGm_TX2_HeightTools
import JGy_LightPadding
import JGr_Counts
import Port4B_Bounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gu_Initial2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem idx01 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s01 s).idx.val.take 1=[16398#u32] := by
  change ((JHc_Gu_Scratch2.s00 s).idx.set (JHc_Gu_Scratch2.s00 s).n (16398#u32)).val.take 1=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s00 s).idx.val.set 0 (16398#u32)).take (0+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s00 s).idx.val.length=16 := (JHc_Gu_Scratch2.s00 s).idx.property
    omega)]
  rfl
#print axioms idx01
theorem idx02 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s02 s).idx.val.take 2=[16398#u32,23374#u32] := by
  change ((JHc_Gu_Scratch2.s01 s).idx.set (JHc_Gu_Scratch2.s01 s).n (23374#u32)).val.take 2=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s01 s).idx.val.set 1 (23374#u32)).take (1+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s01 s).idx.val.length=16 := (JHc_Gu_Scratch2.s01 s).idx.property
    omega)]
  rw [idx01]
  rfl
#print axioms idx02
theorem idx03 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s03 s).idx.val.take 3=[16398#u32,23374#u32,36882#u32] := by
  change ((JHc_Gu_Scratch2.s02 s).idx.set (JHc_Gu_Scratch2.s02 s).n (36882#u32)).val.take 3=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s02 s).idx.val.set 2 (36882#u32)).take (2+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s02 s).idx.val.length=16 := (JHc_Gu_Scratch2.s02 s).idx.property
    omega)]
  rw [idx02]
  rfl
#print axioms idx03
theorem idx04 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s04 s).idx.val.take 4=[16398#u32,23374#u32,36882#u32,39953#u32] := by
  change ((JHc_Gu_Scratch2.s03 s).idx.set (JHc_Gu_Scratch2.s03 s).n (39953#u32)).val.take 4=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s03 s).idx.val.set 3 (39953#u32)).take (3+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s03 s).idx.val.length=16 := (JHc_Gu_Scratch2.s03 s).idx.property
    omega)]
  rw [idx03]
  rfl
#print axioms idx04
theorem idx05 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s05 s).idx.val.take 5=[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32] := by
  change ((JHc_Gu_Scratch2.s04 s).idx.set (JHc_Gu_Scratch2.s04 s).n (45964#u32)).val.take 5=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s04 s).idx.val.set 4 (45964#u32)).take (4+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s04 s).idx.val.length=16 := (JHc_Gu_Scratch2.s04 s).idx.property
    omega)]
  rw [idx04]
  rfl
#print axioms idx05
theorem idx06 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s06 s).idx.val.take 6=[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32] := by
  change ((JHc_Gu_Scratch2.s05 s).idx.set (JHc_Gu_Scratch2.s05 s).n (48079#u32)).val.take 6=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s05 s).idx.val.set 5 (48079#u32)).take (5+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s05 s).idx.val.length=16 := (JHc_Gu_Scratch2.s05 s).idx.property
    omega)]
  rw [idx05]
  rfl
#print axioms idx06
theorem idx07 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s07 s).idx.val.take 7=[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32] := by
  change ((JHc_Gu_Scratch2.s06 s).idx.set (JHc_Gu_Scratch2.s06 s).n (48273#u32)).val.take 7=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s06 s).idx.val.set 6 (48273#u32)).take (6+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s06 s).idx.val.length=16 := (JHc_Gu_Scratch2.s06 s).idx.property
    omega)]
  rw [idx06]
  rfl
#print axioms idx07
theorem idx08 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s08 s).idx.val.take 8=[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32] := by
  change ((JHc_Gu_Scratch2.s07 s).idx.set (JHc_Gu_Scratch2.s07 s).n (52342#u32)).val.take 8=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s07 s).idx.val.set 7 (52342#u32)).take (7+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s07 s).idx.val.length=16 := (JHc_Gu_Scratch2.s07 s).idx.property
    omega)]
  rw [idx07]
  rfl
#print axioms idx08
theorem idx09 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s09 s).idx.val.take 9=[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32] := by
  change ((JHc_Gu_Scratch2.s08 s).idx.set (JHc_Gu_Scratch2.s08 s).n (54205#u32)).val.take 9=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s08 s).idx.val.set 8 (54205#u32)).take (8+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s08 s).idx.val.length=16 := (JHc_Gu_Scratch2.s08 s).idx.property
    omega)]
  rw [idx08]
  rfl
#print axioms idx09
theorem idx10 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s10 s).idx.val.take 10=[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32] := by
  change ((JHc_Gu_Scratch2.s09 s).idx.set (JHc_Gu_Scratch2.s09 s).n (61474#u32)).val.take 10=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s09 s).idx.val.set 9 (61474#u32)).take (9+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s09 s).idx.val.length=16 := (JHc_Gu_Scratch2.s09 s).idx.property
    omega)]
  rw [idx09]
  rfl
#print axioms idx10
theorem val01 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s01 s).val.val.take 1=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s00 s).val.set (JHc_Gu_Scratch2.s00 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩))).val.take 1=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s00 s).val.val.set 0 (encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩))).take (0+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s00 s).val.val.length=16 := (JHc_Gu_Scratch2.s00 s).val.property
    omega)]
  rfl
#print axioms val01
theorem val02 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s02 s).val.val.take 2=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s01 s).val.set (JHc_Gu_Scratch2.s01 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩))).val.take 2=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s01 s).val.val.set 1 (encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩))).take (1+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s01 s).val.val.length=16 := (JHc_Gu_Scratch2.s01 s).val.property
    omega)]
  rw [val01]
  rfl
#print axioms val02
theorem val03 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s03 s).val.val.take 3=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s02 s).val.set (JHc_Gu_Scratch2.s02 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩))).val.take 3=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s02 s).val.val.set 2 (encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩))).take (2+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s02 s).val.val.length=16 := (JHc_Gu_Scratch2.s02 s).val.property
    omega)]
  rw [val02]
  rfl
#print axioms val03
theorem val04 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s04 s).val.val.take 4=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s03 s).val.set (JHc_Gu_Scratch2.s03 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩))).val.take 4=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s03 s).val.val.set 3 (encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩))).take (3+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s03 s).val.val.length=16 := (JHc_Gu_Scratch2.s03 s).val.property
    omega)]
  rw [val03]
  rfl
#print axioms val04
theorem val05 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s05 s).val.val.take 5=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s04 s).val.set (JHc_Gu_Scratch2.s04 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩))).val.take 5=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s04 s).val.val.set 4 (encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩))).take (4+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s04 s).val.val.length=16 := (JHc_Gu_Scratch2.s04 s).val.property
    omega)]
  rw [val04]
  rfl
#print axioms val05
theorem val06 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s06 s).val.val.take 6=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s05 s).val.set (JHc_Gu_Scratch2.s05 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩))).val.take 6=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s05 s).val.val.set 5 (encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩))).take (5+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s05 s).val.val.length=16 := (JHc_Gu_Scratch2.s05 s).val.property
    omega)]
  rw [val05]
  rfl
#print axioms val06
theorem val07 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s07 s).val.val.take 7=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨8,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s06 s).val.set (JHc_Gu_Scratch2.s06 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨8,by decide⟩))).val.take 7=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s06 s).val.val.set 6 (encodeState (JHc_Gu_LeafIteration2.value ⟨8,by decide⟩))).take (6+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s06 s).val.val.length=16 := (JHc_Gu_Scratch2.s06 s).val.property
    omega)]
  rw [val06]
  rfl
#print axioms val07
theorem val08 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s08 s).val.val.take 8=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨8,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨4,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s07 s).val.set (JHc_Gu_Scratch2.s07 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨4,by decide⟩))).val.take 8=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s07 s).val.val.set 7 (encodeState (JHc_Gu_LeafIteration2.value ⟨4,by decide⟩))).take (7+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s07 s).val.val.length=16 := (JHc_Gu_Scratch2.s07 s).val.property
    omega)]
  rw [val07]
  rfl
#print axioms val08
theorem val09 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s09 s).val.val.take 9=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨8,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨4,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨2,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s08 s).val.set (JHc_Gu_Scratch2.s08 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨2,by decide⟩))).val.take 9=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s08 s).val.val.set 8 (encodeState (JHc_Gu_LeafIteration2.value ⟨2,by decide⟩))).take (8+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s08 s).val.val.length=16 := (JHc_Gu_Scratch2.s08 s).val.property
    omega)]
  rw [val08]
  rfl
#print axioms val09
theorem val10 (s : reference.Scratch) :
    (JHc_Gu_Scratch2.s10 s).val.val.take 10=[encodeState (JHc_Gu_LeafIteration2.value ⟨6,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨0,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨1,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨9,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨7,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨5,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨8,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨4,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨2,by decide⟩),encodeState (JHc_Gu_LeafIteration2.value ⟨3,by decide⟩)] := by
  change ((JHc_Gu_Scratch2.s09 s).val.set (JHc_Gu_Scratch2.s09 s).n (encodeState (JHc_Gu_LeafIteration2.value ⟨3,by decide⟩))).val.take 10=_
  rw [Array.set_val_eq]
  change ((JHc_Gu_Scratch2.s09 s).val.val.set 9 (encodeState (JHc_Gu_LeafIteration2.value ⟨3,by decide⟩))).take (9+1)=_
  rw [JGy_G_JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JHc_Gu_Scratch2.s09 s).val.val.length=16 := (JHc_Gu_Scratch2.s09 s).val.property
    omega)]
  rw [val09]
  rfl
#print axioms val10
theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JHc_Gu_Scratch2.s10 s) JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact idx10 s
  · exact val10 s
#print axioms source
end AspisR1.JHc_Gu_Initial2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gu_Levels2
open Aeneas Aeneas.Std Result MultiproofConeRef

def PhaseView (height : Nat) (s : reference.Scratch) : Prop := match height with
  | 0 => JGm_TX2_View.View s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0
  | 1 => JGm_TX2_View.View s JHc_Gu_Level2_01.indices00 JHc_Gu_Level2_01.values00 320
  | 2 => JGm_TX2_View.View s JHc_Gu_Level2_02.indices00 JHc_Gu_Level2_02.values00 640
  | 3 => JGm_TX2_View.View s JHc_Gu_Level2_03.indices00 JHc_Gu_Level2_03.values00 960
  | 4 => JGm_TX2_View.View s JHc_Gu_Level2_04.indices00 JHc_Gu_Level2_04.values00 1280
  | 5 => JGm_TX2_View.View s JHc_Gu_Level2_05.indices00 JHc_Gu_Level2_05.values00 1600
  | 6 => JGm_TX2_View.View s JHc_Gu_Level2_06.indices00 JHc_Gu_Level2_06.values00 1920
  | 7 => JGm_TX2_View.View s JHc_Gu_Level2_07.indices00 JHc_Gu_Level2_07.values00 2240
  | 8 => JGm_TX2_View.View s JHc_Gu_Level2_08.indices00 JHc_Gu_Level2_08.values00 2560
  | 9 => JGm_TX2_View.View s JHc_Gu_Level2_09.indices00 JHc_Gu_Level2_09.values00 2880
  | 10 => JGm_TX2_View.View s JHc_Gu_Level2_10.indices00 JHc_Gu_Level2_10.values00 3200
  | 11 => JGm_TX2_View.View s JHc_Gu_Level2_11.indices00 JHc_Gu_Level2_11.values00 3456
  | 12 => JGm_TX2_View.View s JHc_Gu_Level2_12.indices00 JHc_Gu_Level2_12.values00 3616
  | 13 => JGm_TX2_View.View s JHc_Gu_Level2_13.indices00 JHc_Gu_Level2_13.values00 3712
  | 14 => JGm_TX2_View.View s JHc_Gu_Level2_14.indices00 JHc_Gu_Level2_14.values00 3744
  | 15 => JGm_TX2_View.View s JHc_Gu_Level2_15.indices00 JHc_Gu_Level2_15.values00 3776
  | 16 => JGm_TX2_View.View s JHc_Gu_Level2_16.indices00 JHc_Gu_Level2_16.values00 3776
  | 17 => JGm_TX2_View.View s JHc_Gu_Level2_17.indices00 JHc_Gu_Level2_17.values00 3808
  | 18 => JGm_TX2_View.View s JHc_Gu_Level2_17.indicesOut JHc_Gu_Level2_17.valuesOut 3840
  | _ => False

theorem step {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (h : Nat) (bound : h<18) (s : reference.Scratch) (view : PhaseView h s) :
    ∃ out, reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash s
      JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done out) ∧ PhaseView (h+1) out := by
  interval_cases h
  · exact ⟨_,JHc_Gu_Level2_00.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_01.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_02.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_03.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_04.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_05.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_06.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_07.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_08.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_09.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_10.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_11.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_12.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_13.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_14.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_15.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_16.source D hash s view⟩
  · exact ⟨_,JHc_Gu_Level2_17.source D hash s view⟩
#print axioms step

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch)
    (view : JGm_TX2_View.View s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash s
      JGy_G_JGu_Supplied.nodes2 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JHc_Gu_Level2_17.indicesOut JHc_Gu_Level2_17.valuesOut 3840 := by
  obtain ⟨out,run,last⟩ := JGm_TX2_HeightTools.compose (fun state => reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash state JGy_G_JGu_Supplied.nodes2 0#usize 0#usize) 18 PhaseView (step D hash) s view
  refine ⟨out,?_,last⟩
  rw [MultiproofConeLevelIteration.levels_eq_iteration _ _ _ _ (by decide)]
  exact run
#print axioms source

theorem on_scratch {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    ∃ out, reference.levels (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (JHc_Gu_Scratch2.s10 s) JGy_G_JGu_Supplied.nodes2 18#u32=ok (.Done out) ∧
    JGm_TX2_View.View out JHc_Gu_Level2_17.indicesOut JHc_Gu_Level2_17.valuesOut 3840 :=
  source D hash _ (JHc_Gu_Initial2.source s)
#print axioms on_scratch
end AspisR1.JHc_Gu_Levels2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gu_Valid2
open Aeneas Aeneas.Std Result MultiproofConeRef
 theorem source (s : reference.Scratch)
    (view : JGm_TX2_View.View s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0) :
    reference.valid_indices s.idx 10#usize 0#usize=ok true := by
  have r00 : Array.index_usize s.idx 0#usize=ok 16398#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 0#usize (by decide)
  have r01 : Array.index_usize s.idx 1#usize=ok 23374#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 1#usize (by decide)
  have r02 : Array.index_usize s.idx 2#usize=ok 36882#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 2#usize (by decide)
  have r03 : Array.index_usize s.idx 3#usize=ok 39953#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 3#usize (by decide)
  have r04 : Array.index_usize s.idx 4#usize=ok 45964#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 4#usize (by decide)
  have r05 : Array.index_usize s.idx 5#usize=ok 48079#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 5#usize (by decide)
  have r06 : Array.index_usize s.idx 6#usize=ok 48273#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 6#usize (by decide)
  have r07 : Array.index_usize s.idx 7#usize=ok 52342#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 7#usize (by decide)
  have r08 : Array.index_usize s.idx 8#usize=ok 54205#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 8#usize (by decide)
  have r09 : Array.index_usize s.idx 9#usize=ok 61474#u32 :=
    JGm_TX2_View.index s JHc_Gu_Level2_00.indices00 JHc_Gu_Level2_00.values00 0 view 9#usize (by decide)
  calc
    reference.valid_indices s.idx 10#usize 0#usize=reference.valid_indices s.idx 10#usize 1#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬0#usize≥10#usize),r00]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬16398#u32≥262144#u32)]
      rw [if_neg (by decide : ¬0#usize>0#usize)]
      rw [JGy_G_JGm_TX2_Scalar.add 0#usize 1#usize 1#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 2#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬1#usize≥10#usize),r01]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬23374#u32≥262144#u32)]
      rw [if_pos (by decide : 1#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 1#usize 1#usize 0#usize (by decide) rfl,bind_tc_ok,r00,bind_tc_ok,
        if_neg (by decide : ¬16398#u32≥23374#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 1#usize 1#usize 2#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 3#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬2#usize≥10#usize),r02]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬36882#u32≥262144#u32)]
      rw [if_pos (by decide : 2#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 2#usize 1#usize 1#usize (by decide) rfl,bind_tc_ok,r01,bind_tc_ok,
        if_neg (by decide : ¬23374#u32≥36882#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 2#usize 1#usize 3#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 4#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬3#usize≥10#usize),r03]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬39953#u32≥262144#u32)]
      rw [if_pos (by decide : 3#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 3#usize 1#usize 2#usize (by decide) rfl,bind_tc_ok,r02,bind_tc_ok,
        if_neg (by decide : ¬36882#u32≥39953#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 3#usize 1#usize 4#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 5#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬4#usize≥10#usize),r04]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬45964#u32≥262144#u32)]
      rw [if_pos (by decide : 4#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 4#usize 1#usize 3#usize (by decide) rfl,bind_tc_ok,r03,bind_tc_ok,
        if_neg (by decide : ¬39953#u32≥45964#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 4#usize 1#usize 5#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 6#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬5#usize≥10#usize),r05]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬48079#u32≥262144#u32)]
      rw [if_pos (by decide : 5#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 5#usize 1#usize 4#usize (by decide) rfl,bind_tc_ok,r04,bind_tc_ok,
        if_neg (by decide : ¬45964#u32≥48079#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 5#usize 1#usize 6#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 7#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬6#usize≥10#usize),r06]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬48273#u32≥262144#u32)]
      rw [if_pos (by decide : 6#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 6#usize 1#usize 5#usize (by decide) rfl,bind_tc_ok,r05,bind_tc_ok,
        if_neg (by decide : ¬48079#u32≥48273#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 6#usize 1#usize 7#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 8#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬7#usize≥10#usize),r07]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬52342#u32≥262144#u32)]
      rw [if_pos (by decide : 7#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 7#usize 1#usize 6#usize (by decide) rfl,bind_tc_ok,r06,bind_tc_ok,
        if_neg (by decide : ¬48273#u32≥52342#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 7#usize 1#usize 8#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 9#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬8#usize≥10#usize),r08]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬54205#u32≥262144#u32)]
      rw [if_pos (by decide : 8#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 8#usize 1#usize 7#usize (by decide) rfl,bind_tc_ok,r07,bind_tc_ok,
        if_neg (by decide : ¬52342#u32≥54205#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 8#usize 1#usize 9#usize rfl]
      rfl
    _=reference.valid_indices s.idx 10#usize 10#usize := by
      rw [reference.valid_indices,if_neg (by decide : ¬9#usize≥10#usize),r09]
      simp only [bind_tc_ok]
      rw [if_neg (by decide : ¬61474#u32≥262144#u32)]
      rw [if_pos (by decide : 9#usize>0#usize),JGy_G_JGm_TX2_Scalar.sub 9#usize 1#usize 8#usize (by decide) rfl,bind_tc_ok,r08,bind_tc_ok,
        if_neg (by decide : ¬54205#u32≥61474#u32)]
      rw [JGy_G_JGm_TX2_Scalar.add 9#usize 1#usize 10#usize rfl]
      rfl
    _=ok true := by rw [reference.valid_indices,if_pos (by decide : 10#usize≥10#usize)]
#print axioms source
theorem on_scratch (s : reference.Scratch) :
    reference.valid_indices (JHc_Gu_Scratch2.s10 s).idx 10#usize 0#usize=ok true :=
  source _ (JHc_Gu_Initial2.source s)
#print axioms on_scratch
end AspisR1.JHc_Gu_Valid2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gu_Verify2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes0 JGy_G_JGu_Supplied.nodes1 JGy_G_JGu_Supplied.nodes2

def output {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (s : reference.Scratch) : reference.Scratch := Classical.choose (JHc_Gu_Levels2.on_scratch D hash s)

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    reference.verify_owned (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (encodeState JHc_Gr_M2Root.retainedRoot) (JHc_Gu_Scratch2.s10 s) JGy_G_JGu_Supplied.nodes2=
        ok (true,output D hash s) := by
  obtain ⟨levels,view⟩ := Classical.choose_spec (JHc_Gu_Levels2.on_scratch D hash s)
  have n : (output D hash s).n=1#usize := UScalar.eq_of_val_eq view.size
  have at_eq : (output D hash s).«at»=3840#usize := UScalar.eq_of_val_eq view.at_eq
  have index : Array.index_usize (output D hash s).idx 0#usize=ok 0#u32 :=
    JGm_TX2_View.index _ _ _ _ view 0#usize (by decide)
  have value : Array.index_usize (output D hash s).val 0#usize=ok (encodeState JHc_Gr_M2Roots.value138) :=
    JGm_TX2_View.value _ _ _ _ view 0#usize (by decide)
  rw [JHc_Gr_M2Root.value_eq] at value
  have reset : {JHc_Gu_Scratch2.s10 s with «at»:=0#usize}=JHc_Gu_Scratch2.s10 s := rfl
  have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
  have modulo : 3840#usize % 32#usize=ok 0#usize := by
    obtain ⟨v,run,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=3840#usize) (y:=32#usize) (by scalar_tac))
    have same : v=0#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [same] using run
  have valid : reference.valid_indices (JHc_Gu_Scratch2.s10 s).idx (JHc_Gu_Scratch2.s10 s).n 0#usize=ok true := JHc_Gu_Valid2.on_scratch s
  rw [reference.verify_owned,
    if_neg (by change ¬10#usize=0#usize;decide),
    if_neg (by change ¬10#usize>16#usize;decide),valid]
  simp only [bind_tc_ok,Bool.true_eq,if_true,len,modulo,
    show (0#usize!=0#usize)=false from rfl,Bool.false_eq_true,if_false]
  rw [reset,levels]
  simp only [bind_tc_ok]
  change (do if (output D hash s).n=1#usize then
               let i ← Array.index_usize (output D hash s).idx 0#usize
               if i=0#u32 then
                 let a ← Array.index_usize (output D hash s).val 0#usize
                 let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a (encodeState JHc_Gr_M2Root.retainedRoot)
                 if b then ok (decide ((output D hash s).«at»=3840#usize),output D hash s)
                 else ok (false,output D hash s)
               else ok (false,output D hash s)
             else ok (false,output D hash s))=_
  simp only [n,if_pos rfl,index,value,bind_tc_ok,MultiproofConeLeaf.digest_eq_total,decide_true,
    Bool.true_eq,if_true,at_eq,len]
#print axioms source
end AspisR1.JHc_Gu_Verify2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gw_Terminal2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot2.value

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHc_Gr_M2Root.retainedRoot) 2#usize hash
      0#usize 10#usize 2#usize (JGu_Keys.keys 2)
      (JHc_Gu_Scratch2.s10 s).idx (JHc_Gu_Scratch2.s10 s).val 10#usize 10#usize=
        ok (.done ((JHc_Gu_Verify2.output D hash s).idx,(JHc_Gu_Verify2.output D hash s).val,some (.Ok ()))) := by
  have frontRead : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      (JHc_Gu_Scratch2.s10 s).idx {«end»:=10#usize}=ok JGr_Count2.frontier := by
    simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
    rw [if_pos (by change (10:Nat)≤(JHc_Gu_Scratch2.s10 s).idx.val.length;rw [(JHc_Gu_Scratch2.s10 s).idx.property];decide)]
    apply congrArg ok
    apply Subtype.ext
    exact JHc_Gu_Initial2.idx10 s
  have mul : Usize.wrapping_mul 32#usize 120#usize=3840#usize := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_def]
    scalar_tac
  have fits : (3840#usize).val≤JGp_Slot2.value.val.length := by
    have len : JGp_Slot2.value.val.length=4096 := JGp_Slot2.length
    rw [len]
    decide
  have drop : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JGp_Slot2.value {start:=3840#usize}=ok JGy_G_JGu_Padding2.padding :=
    MultiproofConeSlices.drop_total _ _ fits
  have prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      JGp_Slot2.value {«end»:=3840#usize}=ok JGy_G_JGu_Supplied.nodes2 :=
    MultiproofConeSlices.prefix_total _ _ fits
  obtain ⟨ce,after,chunks,scan⟩ := JGy_G_JGu_PaddingScan.calls (JGy_G_JGc_TX2_RealLeaves.dictionary D)
    JGy_G_JGu_Padding2.padding JGy_G_JGu_Padding2.bytes
  simp only [Port3_BatchStd.install] at scan
  have verify : Port4B_Install.leaves.op10 (JGy_G_JGc_TX2_RealLeaves.dictionary D) hash .Two
      (encodeState JHc_Gr_M2Root.retainedRoot)
      (JHc_Gu_Scratch2.s10 s).idx (JHc_Gu_Scratch2.s10 s).val 10#usize JGy_G_JGu_Supplied.nodes2=
      ok (true,(JHc_Gu_Verify2.output D hash s).idx,(JHc_Gu_Verify2.output D hash s).val) := by
    change (do
      let (b,out) ← reference.verify_owned
        (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
        (encodeState JHc_Gr_M2Root.retainedRoot) (JHc_Gu_Scratch2.s10 s) JGy_G_JGu_Supplied.nodes2
      ok (b,out.idx,out.val))=_
    rw [JHc_Gu_Verify2.source D hash s]
    rfl
  rw [Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body,
    if_neg (by decide : ¬10#usize<10#usize),frontRead]
  have countRead := JGr_Count2.source
  have nodeRead := JGp_Slot2.source
  change Port4B_Install.leaves.op3 JFx_NativeBytes.proof 2#usize=ok JGp_Slot2.value at nodeRead
  change Port4B_Install.leaves.op11 .Two _=_ at countRead
  simp only [bind_tc_ok,Port3_BatchStd.install,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [nodeRead]
  simp only [bind_tc_ok]
  have capacity : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
      2#usize=ok 128#usize := rfl
  rw [capacity]
  simp only [bind_tc_ok,show ¬120#usize>128#usize from by decide,if_false,
    mul,lift,drop,chunks,scan,prefixRead,verify,Bool.false_eq_true,Bool.true_eq,if_true]
  all_goals rfl
#print axioms source

theorem loop {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHc_Gr_M2Root.retainedRoot) 2#usize
      (JHc_Gu_Scratch2.s00 s).idx (JHc_Gu_Scratch2.s00 s).val hash 0#usize 10#usize 2#usize
      (JGu_Keys.keys 2) 0#usize 0#usize=
        ok ((JHc_Gu_Verify2.output D hash s).idx,(JHc_Gu_Verify2.output D hash s).val,some (.Ok ())) := by
  apply (JHc_Gu_Scratch2.source D hash (encodeState JHc_Gr_M2Root.retainedRoot) s).trans
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHc_Gr_M2Root.retainedRoot) 2#usize
      (JHc_Gu_Scratch2.s10 s).idx (JHc_Gu_Scratch2.s10 s).val hash 0#usize 10#usize 2#usize
      (JGu_Keys.keys 2) 10#usize 10#usize=_
  conv_lhs =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,source,bind_tc_ok]
#print axioms loop

end AspisR1.JHc_Gw_Terminal2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gw_Tree2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof JGp_Slot2.value

theorem tree {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof JFo_Prepared.value.queries (encodeState JHc_Gr_M2Root.retainedRoot)
      0#usize 2#usize s.idx s.val hash=
        ok (.Ok (), (JHc_Gu_Verify2.output D hash s).idx,(JHc_Gu_Verify2.output D hash s).val) := by
  have splitCount : Usize.wrapping_sub 10#usize 0#usize=10#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.count 0#usize).1
  have slot : Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 2#usize=2#usize :=
    UScalar.eq_of_val_eq (Port4B_Bounds.slot 0#usize 2#usize (by decide) (by decide))
  have hi : (Port3_BatchStd.install Port4B_Install.leaves).op13=ok 10#usize := rfl
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree
  have bounds : (if (0#usize : Usize)=0#usize then do
      let i ← (Port3_BatchStd.install Port4B_Install.leaves).op13
      ok (0#usize,i)
    else do
      let i ← (Port3_BatchStd.install Port4B_Install.leaves).op13
      ok (i,22#usize))=ok (0#usize,10#usize) := by
    rw [if_pos rfl,hi]
    rfl
  rw [bounds]
  change (do
    let a ← (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize (Usize.wrapping_sub 10#usize 0#usize) 2#usize
    let keys ← (Port3_BatchStd.install Port4B_Install.leaves).op5 a (Usize.wrapping_sub 10#usize 0#usize)
    let (idx,val,pending) ← Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHc_Gr_M2Root.retainedRoot) 2#usize
      s.idx s.val hash 0#usize (Usize.wrapping_sub 10#usize 0#usize) (Usize.wrapping_add (Usize.wrapping_mul 3#usize 0#usize) 2#usize) keys 0#usize 0#usize
    match pending with
    | none => fail .panic
    | some r => ok (r,idx,val))=_
  rw [splitCount,slot]
  have build : (Port3_BatchStd.install Port4B_Install.leaves).op4 JFo_Prepared.value.queries
      0#usize 10#usize 2#usize=ok (JGr_Keys.raw 2) := JGr_Keys.build 2#usize (by decide)
  have sort : (Port3_BatchStd.install Port4B_Install.leaves).op5 (JGr_Keys.raw 2) 10#usize=
      ok (JGu_Keys.keys 2) := JGu_Keys.returned 2
  rw [build,bind_tc_ok,sort,bind_tc_ok]
  have run := JHc_Gw_Terminal2.loop D hash s
  change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install Port4B_Install.leaves) (JGy_G_JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof (encodeState JHc_Gr_M2Root.retainedRoot) 2#usize
      s.idx s.val hash 0#usize 10#usize 2#usize (JGu_Keys.keys 2) 0#usize 0#usize=_ at run
  rw [run]
  rfl
#print axioms tree
end AspisR1.JHc_Gw_Tree2
end
