import R1Z.PV_Inv_MaskChunk0
import R1Z.PV_Inv_MaskChunk1
import R1Z.PV_Inv_MaskChunk2
import R1Z.PV_Inv_MaskTail
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskTable
open R0P
attribute [local irreducible] PV_Inv_MaskSource.mask copyActiveRowMasks

theorem source_equation (block : Fin 64) :
    PV_Inv_MaskSource.mask block = copyActiveRowMasks block := by
  by_cases tail : 48 ≤ block.val
  · exact PV_Inv_MaskTail.source_equation block tail
  rcases block with ⟨b,hb⟩
  have early : b < 48 := by omega
  interval_cases b <;> first
  | exact PV_Inv_MaskChunk0.block_0
  | exact PV_Inv_MaskChunk0.block_1
  | exact PV_Inv_MaskChunk0.block_2
  | exact PV_Inv_MaskChunk0.block_3
  | exact PV_Inv_MaskChunk0.block_4
  | exact PV_Inv_MaskChunk0.block_5
  | exact PV_Inv_MaskChunk0.block_6
  | exact PV_Inv_MaskChunk0.block_7
  | exact PV_Inv_MaskChunk0.block_8
  | exact PV_Inv_MaskChunk0.block_9
  | exact PV_Inv_MaskChunk0.block_10
  | exact PV_Inv_MaskChunk0.block_11
  | exact PV_Inv_MaskChunk0.block_12
  | exact PV_Inv_MaskChunk0.block_13
  | exact PV_Inv_MaskChunk0.block_14
  | exact PV_Inv_MaskChunk0.block_15
  | exact PV_Inv_MaskChunk1.block_16
  | exact PV_Inv_MaskChunk1.block_17
  | exact PV_Inv_MaskChunk1.block_18
  | exact PV_Inv_MaskChunk1.block_19
  | exact PV_Inv_MaskChunk1.block_20
  | exact PV_Inv_MaskChunk1.block_21
  | exact PV_Inv_MaskChunk1.block_22
  | exact PV_Inv_MaskChunk1.block_23
  | exact PV_Inv_MaskChunk1.block_24
  | exact PV_Inv_MaskChunk1.block_25
  | exact PV_Inv_MaskChunk1.block_26
  | exact PV_Inv_MaskChunk1.block_27
  | exact PV_Inv_MaskChunk1.block_28
  | exact PV_Inv_MaskChunk1.block_29
  | exact PV_Inv_MaskChunk1.block_30
  | exact PV_Inv_MaskChunk1.block_31
  | exact PV_Inv_MaskChunk2.block_32
  | exact PV_Inv_MaskChunk2.block_33
  | exact PV_Inv_MaskChunk2.block_34
  | exact PV_Inv_MaskChunk2.block_35
  | exact PV_Inv_MaskChunk2.block_36
  | exact PV_Inv_MaskChunk2.block_37
  | exact PV_Inv_MaskChunk2.block_38
  | exact PV_Inv_MaskChunk2.block_39
  | exact PV_Inv_MaskChunk2.block_40
  | exact PV_Inv_MaskChunk2.block_41
  | exact PV_Inv_MaskChunk2.block_42
  | exact PV_Inv_MaskChunk2.block_43
  | exact PV_Inv_MaskChunk2.block_44
  | exact PV_Inv_MaskChunk2.block_45
  | exact PV_Inv_MaskChunk2.block_46
  | exact PV_Inv_MaskChunk2.block_47

#print axioms source_equation
end R1Z.PV_Inv_MaskTable
