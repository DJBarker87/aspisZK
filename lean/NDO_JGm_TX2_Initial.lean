import NDO_JGk_TX2_ScratchIndices
import NDO_JGm_TX2_Level0_00
import NDO_JGm_TX2_Level1_00
import NDO_JGm_TX2_Level2_00
import NDO_JGm_TX2_View
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Initial0
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem values01 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s01 s).val.val.take 1=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s00 s).val.set (JGk_TX2_Scratch0.s00 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩))).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s00 s).val.val.set 0 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩))).take (0+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s00 s).val.val.length=16 := (JGk_TX2_Scratch0.s00 s).val.property
    omega)]
  rfl
#print axioms values01
theorem values02 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s02 s).val.val.take 2=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s01 s).val.set (JGk_TX2_Scratch0.s01 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩))).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s01 s).val.val.set 1 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩))).take (1+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s01 s).val.val.length=16 := (JGk_TX2_Scratch0.s01 s).val.property
    omega)]
  rw [values01]
  rfl
#print axioms values02
theorem values03 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s03 s).val.val.take 3=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s02 s).val.set (JGk_TX2_Scratch0.s02 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩))).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s02 s).val.val.set 2 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩))).take (2+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s02 s).val.val.length=16 := (JGk_TX2_Scratch0.s02 s).val.property
    omega)]
  rw [values02]
  rfl
#print axioms values03
theorem values04 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s04 s).val.val.take 4=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s03 s).val.set (JGk_TX2_Scratch0.s03 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩))).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s03 s).val.val.set 3 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩))).take (3+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s03 s).val.val.length=16 := (JGk_TX2_Scratch0.s03 s).val.property
    omega)]
  rw [values03]
  rfl
#print axioms values04
theorem values05 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s05 s).val.val.take 5=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s04 s).val.set (JGk_TX2_Scratch0.s04 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩))).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s04 s).val.val.set 4 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩))).take (4+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s04 s).val.val.length=16 := (JGk_TX2_Scratch0.s04 s).val.property
    omega)]
  rw [values04]
  rfl
#print axioms values05
theorem values06 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s06 s).val.val.take 6=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s05 s).val.set (JGk_TX2_Scratch0.s05 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩))).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s05 s).val.val.set 5 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩))).take (5+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s05 s).val.val.length=16 := (JGk_TX2_Scratch0.s05 s).val.property
    omega)]
  rw [values05]
  rfl
#print axioms values06
theorem values07 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s07 s).val.val.take 7=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s06 s).val.set (JGk_TX2_Scratch0.s06 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩))).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s06 s).val.val.set 6 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩))).take (6+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s06 s).val.val.length=16 := (JGk_TX2_Scratch0.s06 s).val.property
    omega)]
  rw [values06]
  rfl
#print axioms values07
theorem values08 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s08 s).val.val.take 8=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s07 s).val.set (JGk_TX2_Scratch0.s07 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩))).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s07 s).val.val.set 7 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩))).take (7+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s07 s).val.val.length=16 := (JGk_TX2_Scratch0.s07 s).val.property
    omega)]
  rw [values07]
  rfl
#print axioms values08
theorem values09 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s09 s).val.val.take 9=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨2,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s08 s).val.set (JGk_TX2_Scratch0.s08 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨2,by decide⟩))).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s08 s).val.val.set 8 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨2,by decide⟩))).take (8+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s08 s).val.val.length=16 := (JGk_TX2_Scratch0.s08 s).val.property
    omega)]
  rw [values08]
  rfl
#print axioms values09
theorem values10 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s10 s).val.val.take 10=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨2,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨6,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s09 s).val.set (JGk_TX2_Scratch0.s09 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨6,by decide⟩))).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s09 s).val.val.set 9 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨6,by decide⟩))).take (9+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s09 s).val.val.length=16 := (JGk_TX2_Scratch0.s09 s).val.property
    omega)]
  rw [values09]
  rfl
#print axioms values10
theorem values11 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s11 s).val.val.take 11=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨2,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨6,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨10,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s10 s).val.set (JGk_TX2_Scratch0.s10 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨10,by decide⟩))).val.take 11=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s10 s).val.val.set 10 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨10,by decide⟩))).take (10+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s10 s).val.val.length=16 := (JGk_TX2_Scratch0.s10 s).val.property
    omega)]
  rw [values10]
  rfl
#print axioms values11
theorem values12 (s : reference.Scratch) :
    (JGk_TX2_Scratch0.s12 s).val.val.take 12=[encodeState (JGk_TX2_NativeLeaves.value0 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨2,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨6,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨10,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value0 ⟨1,by decide⟩)] := by
  change ((JGk_TX2_Scratch0.s11 s).val.set (JGk_TX2_Scratch0.s11 s).n (encodeState (JGk_TX2_NativeLeaves.value0 ⟨1,by decide⟩))).val.take 12=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch0.s11 s).val.val.set 11 (encodeState (JGk_TX2_NativeLeaves.value0 ⟨1,by decide⟩))).take (11+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch0.s11 s).val.val.length=16 := (JGk_TX2_Scratch0.s11 s).val.property
    omega)]
  rw [values11]
  rfl
#print axioms values12
theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JGk_TX2_Scratch0.s12 s) JGm_TX2_Level0_00.indices00 JGm_TX2_Level0_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact JGk_TX2_ScratchIndices.front0_12 s
  · exact values12 s
#print axioms source
end AspisR1.JGm_TX2_Initial0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Initial1
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem values01 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s01 s).val.val.take 1=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s00 s).val.set (JGk_TX2_Scratch1.s00 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩))).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s00 s).val.val.set 0 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩))).take (0+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s00 s).val.val.length=16 := (JGk_TX2_Scratch1.s00 s).val.property
    omega)]
  rfl
#print axioms values01
theorem values02 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s02 s).val.val.take 2=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s01 s).val.set (JGk_TX2_Scratch1.s01 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩))).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s01 s).val.val.set 1 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩))).take (1+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s01 s).val.val.length=16 := (JGk_TX2_Scratch1.s01 s).val.property
    omega)]
  rw [values01]
  rfl
#print axioms values02
theorem values03 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s03 s).val.val.take 3=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s02 s).val.set (JGk_TX2_Scratch1.s02 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩))).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s02 s).val.val.set 2 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩))).take (2+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s02 s).val.val.length=16 := (JGk_TX2_Scratch1.s02 s).val.property
    omega)]
  rw [values02]
  rfl
#print axioms values03
theorem values04 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s04 s).val.val.take 4=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s03 s).val.set (JGk_TX2_Scratch1.s03 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩))).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s03 s).val.val.set 3 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩))).take (3+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s03 s).val.val.length=16 := (JGk_TX2_Scratch1.s03 s).val.property
    omega)]
  rw [values03]
  rfl
#print axioms values04
theorem values05 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s05 s).val.val.take 5=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s04 s).val.set (JGk_TX2_Scratch1.s04 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩))).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s04 s).val.val.set 4 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩))).take (4+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s04 s).val.val.length=16 := (JGk_TX2_Scratch1.s04 s).val.property
    omega)]
  rw [values04]
  rfl
#print axioms values05
theorem values06 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s06 s).val.val.take 6=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s05 s).val.set (JGk_TX2_Scratch1.s05 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩))).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s05 s).val.val.set 5 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩))).take (5+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s05 s).val.val.length=16 := (JGk_TX2_Scratch1.s05 s).val.property
    omega)]
  rw [values05]
  rfl
#print axioms values06
theorem values07 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s07 s).val.val.take 7=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s06 s).val.set (JGk_TX2_Scratch1.s06 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩))).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s06 s).val.val.set 6 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩))).take (6+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s06 s).val.val.length=16 := (JGk_TX2_Scratch1.s06 s).val.property
    omega)]
  rw [values06]
  rfl
#print axioms values07
theorem values08 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s08 s).val.val.take 8=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s07 s).val.set (JGk_TX2_Scratch1.s07 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩))).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s07 s).val.val.set 7 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩))).take (7+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s07 s).val.val.length=16 := (JGk_TX2_Scratch1.s07 s).val.property
    omega)]
  rw [values07]
  rfl
#print axioms values08
theorem values09 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s09 s).val.val.take 9=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s08 s).val.set (JGk_TX2_Scratch1.s08 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩))).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s08 s).val.val.set 8 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩))).take (8+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s08 s).val.val.length=16 := (JGk_TX2_Scratch1.s08 s).val.property
    omega)]
  rw [values08]
  rfl
#print axioms values09
theorem values10 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s10 s).val.val.take 10=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s09 s).val.set (JGk_TX2_Scratch1.s09 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩))).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s09 s).val.val.set 9 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩))).take (9+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s09 s).val.val.length=16 := (JGk_TX2_Scratch1.s09 s).val.property
    omega)]
  rw [values09]
  rfl
#print axioms values10
theorem values11 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s11 s).val.val.take 11=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s10 s).val.set (JGk_TX2_Scratch1.s10 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩))).val.take 11=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s10 s).val.val.set 10 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩))).take (10+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s10 s).val.val.length=16 := (JGk_TX2_Scratch1.s10 s).val.property
    omega)]
  rw [values10]
  rfl
#print axioms values11
theorem values12 (s : reference.Scratch) :
    (JGk_TX2_Scratch1.s12 s).val.val.take 12=[encodeState (JGk_TX2_NativeLeaves.value1 ⟨11,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨7,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨5,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨9,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨8,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨0,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨3,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨4,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨2,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨6,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨10,by decide⟩),encodeState (JGk_TX2_NativeLeaves.value1 ⟨1,by decide⟩)] := by
  change ((JGk_TX2_Scratch1.s11 s).val.set (JGk_TX2_Scratch1.s11 s).n (encodeState (JGk_TX2_NativeLeaves.value1 ⟨1,by decide⟩))).val.take 12=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch1.s11 s).val.val.set 11 (encodeState (JGk_TX2_NativeLeaves.value1 ⟨1,by decide⟩))).take (11+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch1.s11 s).val.val.length=16 := (JGk_TX2_Scratch1.s11 s).val.property
    omega)]
  rw [values11]
  rfl
#print axioms values12
theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JGk_TX2_Scratch1.s12 s) JGm_TX2_Level1_00.indices00 JGm_TX2_Level1_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact JGk_TX2_ScratchIndices.front1_12 s
  · exact values12 s
#print axioms source
end AspisR1.JGm_TX2_Initial1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_Initial2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem values01 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s01 s).val.val.take 1=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s00 s).val.set (JGk_TX2_Scratch2.s00 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩))).val.take 1=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s00 s).val.val.set 0 (encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩))).take (0+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s00 s).val.val.length=16 := (JGk_TX2_Scratch2.s00 s).val.property
    omega)]
  rfl
#print axioms values01
theorem values02 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s02 s).val.val.take 2=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s01 s).val.set (JGk_TX2_Scratch2.s01 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩))).val.take 2=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s01 s).val.val.set 1 (encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩))).take (1+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s01 s).val.val.length=16 := (JGk_TX2_Scratch2.s01 s).val.property
    omega)]
  rw [values01]
  rfl
#print axioms values02
theorem values03 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s03 s).val.val.take 3=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s02 s).val.set (JGk_TX2_Scratch2.s02 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩))).val.take 3=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s02 s).val.val.set 2 (encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩))).take (2+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s02 s).val.val.length=16 := (JGk_TX2_Scratch2.s02 s).val.property
    omega)]
  rw [values02]
  rfl
#print axioms values03
theorem values04 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s04 s).val.val.take 4=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s03 s).val.set (JGk_TX2_Scratch2.s03 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩))).val.take 4=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s03 s).val.val.set 3 (encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩))).take (3+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s03 s).val.val.length=16 := (JGk_TX2_Scratch2.s03 s).val.property
    omega)]
  rw [values03]
  rfl
#print axioms values04
theorem values05 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s05 s).val.val.take 5=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s04 s).val.set (JGk_TX2_Scratch2.s04 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩))).val.take 5=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s04 s).val.val.set 4 (encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩))).take (4+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s04 s).val.val.length=16 := (JGk_TX2_Scratch2.s04 s).val.property
    omega)]
  rw [values04]
  rfl
#print axioms values05
theorem values06 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s06 s).val.val.take 6=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s05 s).val.set (JGk_TX2_Scratch2.s05 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩))).val.take 6=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s05 s).val.val.set 5 (encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩))).take (5+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s05 s).val.val.length=16 := (JGk_TX2_Scratch2.s05 s).val.property
    omega)]
  rw [values05]
  rfl
#print axioms values06
theorem values07 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s07 s).val.val.take 7=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s06 s).val.set (JGk_TX2_Scratch2.s06 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩))).val.take 7=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s06 s).val.val.set 6 (encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩))).take (6+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s06 s).val.val.length=16 := (JGk_TX2_Scratch2.s06 s).val.property
    omega)]
  rw [values06]
  rfl
#print axioms values07
theorem values08 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s08 s).val.val.take 8=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s07 s).val.set (JGk_TX2_Scratch2.s07 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩))).val.take 8=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s07 s).val.val.set 7 (encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩))).take (7+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s07 s).val.val.length=16 := (JGk_TX2_Scratch2.s07 s).val.property
    omega)]
  rw [values07]
  rfl
#print axioms values08
theorem values09 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s09 s).val.val.take 9=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨2,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s08 s).val.set (JGk_TX2_Scratch2.s08 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨2,by decide⟩))).val.take 9=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s08 s).val.val.set 8 (encodeState (JGc_TX2_RealLeaves.value ⟨2,by decide⟩))).take (8+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s08 s).val.val.length=16 := (JGk_TX2_Scratch2.s08 s).val.property
    omega)]
  rw [values08]
  rfl
#print axioms values09
theorem values10 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s10 s).val.val.take 10=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨2,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨6,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s09 s).val.set (JGk_TX2_Scratch2.s09 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨6,by decide⟩))).val.take 10=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s09 s).val.val.set 9 (encodeState (JGc_TX2_RealLeaves.value ⟨6,by decide⟩))).take (9+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s09 s).val.val.length=16 := (JGk_TX2_Scratch2.s09 s).val.property
    omega)]
  rw [values09]
  rfl
#print axioms values10
theorem values11 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s11 s).val.val.take 11=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨2,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨6,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨10,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s10 s).val.set (JGk_TX2_Scratch2.s10 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨10,by decide⟩))).val.take 11=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s10 s).val.val.set 10 (encodeState (JGc_TX2_RealLeaves.value ⟨10,by decide⟩))).take (10+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s10 s).val.val.length=16 := (JGk_TX2_Scratch2.s10 s).val.property
    omega)]
  rw [values10]
  rfl
#print axioms values11
theorem values12 (s : reference.Scratch) :
    (JGk_TX2_Scratch2.s12 s).val.val.take 12=[encodeState (JGc_TX2_RealLeaves.value ⟨11,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨7,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨5,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨9,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨8,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨0,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨3,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨4,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨2,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨6,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨10,by decide⟩),encodeState (JGc_TX2_RealLeaves.value ⟨1,by decide⟩)] := by
  change ((JGk_TX2_Scratch2.s11 s).val.set (JGk_TX2_Scratch2.s11 s).n (encodeState (JGc_TX2_RealLeaves.value ⟨1,by decide⟩))).val.take 12=_
  rw [Array.set_val_eq]
  change ((JGk_TX2_Scratch2.s11 s).val.val.set 11 (encodeState (JGc_TX2_RealLeaves.value ⟨1,by decide⟩))).take (11+1)=_
  rw [JGk_TX2_ScratchIndices.snoc_set _ _ _ (by
    have len : (JGk_TX2_Scratch2.s11 s).val.val.length=16 := (JGk_TX2_Scratch2.s11 s).val.property
    omega)]
  rw [values11]
  rfl
#print axioms values12
theorem source (s : reference.Scratch) :
    JGm_TX2_View.View (JGk_TX2_Scratch2.s12 s) JGm_TX2_Level2_00.indices00 JGm_TX2_Level2_00.values00 0 := by
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · exact JGk_TX2_ScratchIndices.front2_12 s
  · exact values12 s
#print axioms source
end AspisR1.JGm_TX2_Initial2
end
