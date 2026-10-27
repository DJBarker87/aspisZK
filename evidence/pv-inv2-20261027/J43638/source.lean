import R1Z.PV_Inv_ActiveChunk00
import R1Z.PV_Inv_ActiveChunk01
import R1Z.PV_Inv_ActiveChunk02
import R1Z.PV_Inv_ActiveChunk03
import R1Z.PV_Inv_ActiveChunk04
import R1Z.PV_Inv_ActiveChunk05
import R1Z.PV_Inv_ActiveChunk06
import R1Z.PV_Inv_ActiveChunk07
import R1Z.PV_Inv_ActiveChunk08
import R1Z.PV_Inv_ActiveChunk09
import R1Z.PV_Inv_ActiveChunk10
import R1Z.PV_Inv_ActiveChunk11
import R1Z.PV_Inv_ActiveChunk12
import R1Z.PV_Inv_ActiveChunk13
import R1Z.PV_Inv_ActiveChunk14
import R1Z.PV_Inv_ActiveChunk15
import R1Z.PV_Inv_ActiveChunk16
import R1Z.PV_Inv_ActiveChunk17
import R1Z.PV_Inv_ActiveChunk18
import R1Z.PV_Inv_ActiveChunk19
import R1Z.PV_Inv_ActiveChunk20
import R1Z.PV_Inv_ActiveChunk21
import R1Z.PV_Inv_ActiveChunk22
import R1Z.PV_Inv_ActiveChunk23
import R1Z.PV_Inv_ActiveChunk24
import R1Z.PV_Inv_ActiveChunk25
import R1Z.PV_Inv_ActiveChunk26
import R1Z.PV_Inv_ActiveChunk27
import R1Z.PV_Inv_ActiveChunk28
import R1Z.PV_Inv_ActiveChunk29
import R1Z.PV_Inv_ActiveChunk30
import R1Z.PV_Inv_ActiveChunk31
import R1Z.PV_Inv_ActiveChunk32
import R1Z.PV_Inv_ActiveChunk33
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveRegistry
open R0P

def chunks : List CopyLink :=
  PV_Inv_ActiveChunk00.links ++
  PV_Inv_ActiveChunk01.links ++
  PV_Inv_ActiveChunk02.links ++
  PV_Inv_ActiveChunk03.links ++
  PV_Inv_ActiveChunk04.links ++
  PV_Inv_ActiveChunk05.links ++
  PV_Inv_ActiveChunk06.links ++
  PV_Inv_ActiveChunk07.links ++
  PV_Inv_ActiveChunk08.links ++
  PV_Inv_ActiveChunk09.links ++
  PV_Inv_ActiveChunk10.links ++
  PV_Inv_ActiveChunk11.links ++
  PV_Inv_ActiveChunk12.links ++
  PV_Inv_ActiveChunk13.links ++
  PV_Inv_ActiveChunk14.links ++
  PV_Inv_ActiveChunk15.links ++
  PV_Inv_ActiveChunk16.links ++
  PV_Inv_ActiveChunk17.links ++
  PV_Inv_ActiveChunk18.links ++
  PV_Inv_ActiveChunk19.links ++
  PV_Inv_ActiveChunk20.links ++
  PV_Inv_ActiveChunk21.links ++
  PV_Inv_ActiveChunk22.links ++
  PV_Inv_ActiveChunk23.links ++
  PV_Inv_ActiveChunk24.links ++
  PV_Inv_ActiveChunk25.links ++
  PV_Inv_ActiveChunk26.links ++
  PV_Inv_ActiveChunk27.links ++
  PV_Inv_ActiveChunk28.links ++
  PV_Inv_ActiveChunk29.links ++
  PV_Inv_ActiveChunk30.links ++
  PV_Inv_ActiveChunk31.links ++
  PV_Inv_ActiveChunk32.links ++
  PV_Inv_ActiveChunk33.links

/-- Literal descriptor equality only: no field computation, no native-enumerator claim. -/
theorem exact_table : chunks = copyLinks := by rfl

theorem active (l : CopyLink) (hl : l ∈ copyLinks) :
    CopyActiveRow l.producer.row ∧ CopyActiveRow l.consumer.row := by
  rw [←exact_table] at hl
  simp only [chunks,List.mem_append] at hl
  rcases hl with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33
  · exact PV_Inv_ActiveChunk00.active l h0
  · exact PV_Inv_ActiveChunk01.active l h1
  · exact PV_Inv_ActiveChunk02.active l h2
  · exact PV_Inv_ActiveChunk03.active l h3
  · exact PV_Inv_ActiveChunk04.active l h4
  · exact PV_Inv_ActiveChunk05.active l h5
  · exact PV_Inv_ActiveChunk06.active l h6
  · exact PV_Inv_ActiveChunk07.active l h7
  · exact PV_Inv_ActiveChunk08.active l h8
  · exact PV_Inv_ActiveChunk09.active l h9
  · exact PV_Inv_ActiveChunk10.active l h10
  · exact PV_Inv_ActiveChunk11.active l h11
  · exact PV_Inv_ActiveChunk12.active l h12
  · exact PV_Inv_ActiveChunk13.active l h13
  · exact PV_Inv_ActiveChunk14.active l h14
  · exact PV_Inv_ActiveChunk15.active l h15
  · exact PV_Inv_ActiveChunk16.active l h16
  · exact PV_Inv_ActiveChunk17.active l h17
  · exact PV_Inv_ActiveChunk18.active l h18
  · exact PV_Inv_ActiveChunk19.active l h19
  · exact PV_Inv_ActiveChunk20.active l h20
  · exact PV_Inv_ActiveChunk21.active l h21
  · exact PV_Inv_ActiveChunk22.active l h22
  · exact PV_Inv_ActiveChunk23.active l h23
  · exact PV_Inv_ActiveChunk24.active l h24
  · exact PV_Inv_ActiveChunk25.active l h25
  · exact PV_Inv_ActiveChunk26.active l h26
  · exact PV_Inv_ActiveChunk27.active l h27
  · exact PV_Inv_ActiveChunk28.active l h28
  · exact PV_Inv_ActiveChunk29.active l h29
  · exact PV_Inv_ActiveChunk30.active l h30
  · exact PV_Inv_ActiveChunk31.active l h31
  · exact PV_Inv_ActiveChunk32.active l h32
  · exact PV_Inv_ActiveChunk33.active l h33

theorem tag_bound (l : CopyLink) (hl : l ∈ copyLinks) : l.tag < 2147483647 := by
  rw [←exact_table] at hl
  simp only [chunks,List.mem_append] at hl
  rcases hl with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33
  · exact PV_Inv_ActiveChunk00.tag_bound l h0
  · exact PV_Inv_ActiveChunk01.tag_bound l h1
  · exact PV_Inv_ActiveChunk02.tag_bound l h2
  · exact PV_Inv_ActiveChunk03.tag_bound l h3
  · exact PV_Inv_ActiveChunk04.tag_bound l h4
  · exact PV_Inv_ActiveChunk05.tag_bound l h5
  · exact PV_Inv_ActiveChunk06.tag_bound l h6
  · exact PV_Inv_ActiveChunk07.tag_bound l h7
  · exact PV_Inv_ActiveChunk08.tag_bound l h8
  · exact PV_Inv_ActiveChunk09.tag_bound l h9
  · exact PV_Inv_ActiveChunk10.tag_bound l h10
  · exact PV_Inv_ActiveChunk11.tag_bound l h11
  · exact PV_Inv_ActiveChunk12.tag_bound l h12
  · exact PV_Inv_ActiveChunk13.tag_bound l h13
  · exact PV_Inv_ActiveChunk14.tag_bound l h14
  · exact PV_Inv_ActiveChunk15.tag_bound l h15
  · exact PV_Inv_ActiveChunk16.tag_bound l h16
  · exact PV_Inv_ActiveChunk17.tag_bound l h17
  · exact PV_Inv_ActiveChunk18.tag_bound l h18
  · exact PV_Inv_ActiveChunk19.tag_bound l h19
  · exact PV_Inv_ActiveChunk20.tag_bound l h20
  · exact PV_Inv_ActiveChunk21.tag_bound l h21
  · exact PV_Inv_ActiveChunk22.tag_bound l h22
  · exact PV_Inv_ActiveChunk23.tag_bound l h23
  · exact PV_Inv_ActiveChunk24.tag_bound l h24
  · exact PV_Inv_ActiveChunk25.tag_bound l h25
  · exact PV_Inv_ActiveChunk26.tag_bound l h26
  · exact PV_Inv_ActiveChunk27.tag_bound l h27
  · exact PV_Inv_ActiveChunk28.tag_bound l h28
  · exact PV_Inv_ActiveChunk29.tag_bound l h29
  · exact PV_Inv_ActiveChunk30.tag_bound l h30
  · exact PV_Inv_ActiveChunk31.tag_bound l h31
  · exact PV_Inv_ActiveChunk32.tag_bound l h32
  · exact PV_Inv_ActiveChunk33.tag_bound l h33

#print axioms exact_table
#print axioms active
#print axioms tag_bound
end R1Z.PV_Inv_ActiveRegistry
