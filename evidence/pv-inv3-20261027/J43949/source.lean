import R1Z.PV_Inv_MaskPartition
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskTail60
open R0P
theorem installed_table : copyActiveRowMasks 60 = 26214 := by rfl
#print axioms installed_table
theorem contribution00 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk00.links 60 = 0 := by rfl
#print axioms contribution00
theorem contribution01 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk01.links 60 = 0 := by rfl
#print axioms contribution01
theorem contribution02 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk02.links 60 = 0 := by rfl
#print axioms contribution02
theorem contribution03 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk03.links 60 = 0 := by rfl
#print axioms contribution03
theorem contribution04 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk04.links 60 = 0 := by rfl
#print axioms contribution04
theorem contribution05 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk05.links 60 = 0 := by rfl
#print axioms contribution05
theorem contribution06 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk06.links 60 = 0 := by rfl
#print axioms contribution06
theorem contribution07 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk07.links 60 = 0 := by rfl
#print axioms contribution07
theorem contribution08 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk08.links 60 = 0 := by rfl
#print axioms contribution08
theorem contribution09 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk09.links 60 = 0 := by rfl
#print axioms contribution09
theorem contribution10 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk10.links 60 = 0 := by rfl
#print axioms contribution10
theorem contribution11 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk11.links 60 = 0 := by rfl
#print axioms contribution11
theorem contribution12 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk12.links 60 = 0 := by rfl
#print axioms contribution12
theorem contribution13 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk13.links 60 = 0 := by rfl
#print axioms contribution13
theorem contribution14 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk14.links 60 = 0 := by rfl
#print axioms contribution14
theorem contribution15 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk15.links 60 = 0 := by rfl
#print axioms contribution15
theorem contribution16 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk16.links 60 = 0 := by rfl
#print axioms contribution16
theorem contribution17 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk17.links 60 = 0 := by rfl
#print axioms contribution17
theorem contribution18 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk18.links 60 = 0 := by rfl
#print axioms contribution18
theorem contribution19 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk19.links 60 = 0 := by rfl
#print axioms contribution19
theorem contribution20 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk20.links 60 = 0 := by rfl
#print axioms contribution20
theorem contribution21 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk21.links 60 = 0 := by rfl
#print axioms contribution21
theorem contribution22 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk22.links 60 = 0 := by rfl
#print axioms contribution22
theorem contribution23 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk23.links 60 = 0 := by rfl
#print axioms contribution23
theorem contribution24 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk24.links 60 = 0 := by rfl
#print axioms contribution24
theorem contribution25 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk25.links 60 = 38 := by rfl
#print axioms contribution25
theorem contribution26 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk26.links 60 = 1600 := by rfl
#print axioms contribution26
theorem contribution27 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk27.links 60 = 25600 := by rfl
#print axioms contribution27
theorem contribution28 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk28.links 60 = 0 := by rfl
#print axioms contribution28
theorem contribution29 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk29.links 60 = 0 := by rfl
#print axioms contribution29
theorem contribution30 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk30.links 60 = 0 := by rfl
#print axioms contribution30
theorem contribution31 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk31.links 60 = 0 := by rfl
#print axioms contribution31
theorem contribution32 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk32.links 60 = 0 := by rfl
#print axioms contribution32
theorem contribution33 : PV_Inv_MaskPartition.maskOn PV_Inv_ActiveChunk33.links 60 = 0 := by rfl
#print axioms contribution33
theorem block : PV_Inv_MaskSource.mask 60 = copyActiveRowMasks 60 := by
  rw [installed_table,PV_Inv_MaskPartition.decomposition,contribution00,contribution01,contribution02,contribution03,contribution04,contribution05,contribution06,contribution07,contribution08,contribution09,contribution10,contribution11,contribution12,contribution13,contribution14,contribution15,contribution16,contribution17,contribution18,contribution19,contribution20,contribution21,contribution22,contribution23,contribution24,contribution25,contribution26,contribution27,contribution28,contribution29,contribution30,contribution31,contribution32,contribution33]
  rfl
#print axioms block
end R1Z.PV_Inv_MaskTail60
