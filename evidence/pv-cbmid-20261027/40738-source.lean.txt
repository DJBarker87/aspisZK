import R1Z.PV_CBM_CellsMaterializer
import R1Z.PV_CBM_ListComposition
namespace R1Z.PV_CBM_CellsSpec
open Aeneas Aeneas.Std Result
set_option autoImplicit false
-- Keep literal blocks abstract during composition; their facts are checked separately.
attribute [local irreducible] PV_CBM_CellChunk00.literals PV_CBM_CellChunk01.literals PV_CBM_CellChunk02.literals PV_CBM_CellChunk03.literals PV_CBM_CellChunk04.literals PV_CBM_CellChunk05.literals PV_CBM_CellChunk06.literals PV_CBM_CellChunk07.literals PV_CBM_CellChunk08.literals PV_CBM_CellChunk09.literals PV_CBM_CellChunk10.literals PV_CBM_CellChunk11.literals PV_CBM_CellChunk12.literals PV_CBM_CellChunk13.literals PV_CBM_CellChunk14.literals PV_CBM_CellChunk15.literals PV_CBM_CellChunk16.literals PV_CBM_CellChunk17.literals PV_CBM_CellChunk18.literals PV_CBM_CellChunk19.literals PV_CBM_CellChunk20.literals PV_CBM_CellChunk21.literals PV_CBM_CellChunk22.literals PV_CBM_CellChunk23.literals PV_CBM_CellChunk24.literals PV_CBM_CellChunk25.literals PV_CBM_CellChunk26.literals PV_CBM_CellChunk27.literals PV_CBM_CellChunk28.literals PV_CBM_CellChunk29.literals PV_CBM_CellChunk30.literals PV_CBM_CellChunk31.literals PV_CBM_CellChunk32.literals PV_CBM_CellChunk33.literals PV_CBM_CellChunk34.literals PV_CBM_CellChunk35.literals PV_CBM_CellChunk36.literals PV_CBM_CellChunk37.literals PV_CBM_CellChunk38.literals PV_CBM_CellChunk39.literals PV_CBM_CellChunk40.literals PV_CBM_CellChunk41.literals PV_CBM_CellChunk42.literals PV_CBM_CellChunk43.literals PV_CBM_CellChunk44.literals PV_CBM_CellChunk45.literals PV_CBM_CellChunk46.literals PV_CBM_CellChunk47.literals PV_CBM_CellChunk48.literals PV_CBM_CellChunk49.literals PV_CBM_CellChunk50.literals PV_CBM_CellChunk51.literals PV_CBM_CellChunk52.literals PV_CBM_CellChunk53.literals PV_CBM_CellChunk54.literals PV_CBM_CellChunk55.literals PV_CBM_CellChunk56.literals PV_CBM_CellChunk57.literals PV_CBM_CellChunk58.literals PV_CBM_CellChunk59.literals
abbrev Cell := ProverRwFull.aspis_statement.trace_v4.TraceCell
def literals : List Cell :=
  PV_CBM_CellChunk00.literals ++
  PV_CBM_CellChunk01.literals ++
  PV_CBM_CellChunk02.literals ++
  PV_CBM_CellChunk03.literals ++
  PV_CBM_CellChunk04.literals ++
  PV_CBM_CellChunk05.literals ++
  PV_CBM_CellChunk06.literals ++
  PV_CBM_CellChunk07.literals ++
  PV_CBM_CellChunk08.literals ++
  PV_CBM_CellChunk09.literals ++
  PV_CBM_CellChunk10.literals ++
  PV_CBM_CellChunk11.literals ++
  PV_CBM_CellChunk12.literals ++
  PV_CBM_CellChunk13.literals ++
  PV_CBM_CellChunk14.literals ++
  PV_CBM_CellChunk15.literals ++
  PV_CBM_CellChunk16.literals ++
  PV_CBM_CellChunk17.literals ++
  PV_CBM_CellChunk18.literals ++
  PV_CBM_CellChunk19.literals ++
  PV_CBM_CellChunk20.literals ++
  PV_CBM_CellChunk21.literals ++
  PV_CBM_CellChunk22.literals ++
  PV_CBM_CellChunk23.literals ++
  PV_CBM_CellChunk24.literals ++
  PV_CBM_CellChunk25.literals ++
  PV_CBM_CellChunk26.literals ++
  PV_CBM_CellChunk27.literals ++
  PV_CBM_CellChunk28.literals ++
  PV_CBM_CellChunk29.literals ++
  PV_CBM_CellChunk30.literals ++
  PV_CBM_CellChunk31.literals ++
  PV_CBM_CellChunk32.literals ++
  PV_CBM_CellChunk33.literals ++
  PV_CBM_CellChunk34.literals ++
  PV_CBM_CellChunk35.literals ++
  PV_CBM_CellChunk36.literals ++
  PV_CBM_CellChunk37.literals ++
  PV_CBM_CellChunk38.literals ++
  PV_CBM_CellChunk39.literals ++
  PV_CBM_CellChunk40.literals ++
  PV_CBM_CellChunk41.literals ++
  PV_CBM_CellChunk42.literals ++
  PV_CBM_CellChunk43.literals ++
  PV_CBM_CellChunk44.literals ++
  PV_CBM_CellChunk45.literals ++
  PV_CBM_CellChunk46.literals ++
  PV_CBM_CellChunk47.literals ++
  PV_CBM_CellChunk48.literals ++
  PV_CBM_CellChunk49.literals ++
  PV_CBM_CellChunk50.literals ++
  PV_CBM_CellChunk51.literals ++
  PV_CBM_CellChunk52.literals ++
  PV_CBM_CellChunk53.literals ++
  PV_CBM_CellChunk54.literals ++
  PV_CBM_CellChunk55.literals ++
  PV_CBM_CellChunk56.literals ++
  PV_CBM_CellChunk57.literals ++
  PV_CBM_CellChunk58.literals ++
  PV_CBM_CellChunk59.literals
theorem length : literals.length = 3803 := by
  simp only [literals,List.length_append,PV_CBM_CellChunk00.length,PV_CBM_CellChunk01.length,PV_CBM_CellChunk02.length,PV_CBM_CellChunk03.length,PV_CBM_CellChunk04.length,PV_CBM_CellChunk05.length,PV_CBM_CellChunk06.length,PV_CBM_CellChunk07.length,PV_CBM_CellChunk08.length,PV_CBM_CellChunk09.length,PV_CBM_CellChunk10.length,PV_CBM_CellChunk11.length,PV_CBM_CellChunk12.length,PV_CBM_CellChunk13.length,PV_CBM_CellChunk14.length,PV_CBM_CellChunk15.length,PV_CBM_CellChunk16.length,PV_CBM_CellChunk17.length,PV_CBM_CellChunk18.length,PV_CBM_CellChunk19.length,PV_CBM_CellChunk20.length,PV_CBM_CellChunk21.length,PV_CBM_CellChunk22.length,PV_CBM_CellChunk23.length,PV_CBM_CellChunk24.length,PV_CBM_CellChunk25.length,PV_CBM_CellChunk26.length,PV_CBM_CellChunk27.length,PV_CBM_CellChunk28.length,PV_CBM_CellChunk29.length,PV_CBM_CellChunk30.length,PV_CBM_CellChunk31.length,PV_CBM_CellChunk32.length,PV_CBM_CellChunk33.length,PV_CBM_CellChunk34.length,PV_CBM_CellChunk35.length,PV_CBM_CellChunk36.length,PV_CBM_CellChunk37.length,PV_CBM_CellChunk38.length,PV_CBM_CellChunk39.length,PV_CBM_CellChunk40.length,PV_CBM_CellChunk41.length,PV_CBM_CellChunk42.length,PV_CBM_CellChunk43.length,PV_CBM_CellChunk44.length,PV_CBM_CellChunk45.length,PV_CBM_CellChunk46.length,PV_CBM_CellChunk47.length,PV_CBM_CellChunk48.length,PV_CBM_CellChunk49.length,PV_CBM_CellChunk50.length,PV_CBM_CellChunk51.length,PV_CBM_CellChunk52.length,PV_CBM_CellChunk53.length,PV_CBM_CellChunk54.length,PV_CBM_CellChunk55.length,PV_CBM_CellChunk56.length,PV_CBM_CellChunk57.length,PV_CBM_CellChunk58.length,PV_CBM_CellChunk59.length]
theorem all_free : ∀ cell ∈ literals, PV_CBM_InventoryShape.free cell.row.val cell.column.val := by
  unfold literals
  exact PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_ListComposition.append_free (PV_CBM_CellChunk00.literals_free) PV_CBM_CellChunk01.literals_free) PV_CBM_CellChunk02.literals_free) PV_CBM_CellChunk03.literals_free) PV_CBM_CellChunk04.literals_free) PV_CBM_CellChunk05.literals_free) PV_CBM_CellChunk06.literals_free) PV_CBM_CellChunk07.literals_free) PV_CBM_CellChunk08.literals_free) PV_CBM_CellChunk09.literals_free) PV_CBM_CellChunk10.literals_free) PV_CBM_CellChunk11.literals_free) PV_CBM_CellChunk12.literals_free) PV_CBM_CellChunk13.literals_free) PV_CBM_CellChunk14.literals_free) PV_CBM_CellChunk15.literals_free) PV_CBM_CellChunk16.literals_free) PV_CBM_CellChunk17.literals_free) PV_CBM_CellChunk18.literals_free) PV_CBM_CellChunk19.literals_free) PV_CBM_CellChunk20.literals_free) PV_CBM_CellChunk21.literals_free) PV_CBM_CellChunk22.literals_free) PV_CBM_CellChunk23.literals_free) PV_CBM_CellChunk24.literals_free) PV_CBM_CellChunk25.literals_free) PV_CBM_CellChunk26.literals_free) PV_CBM_CellChunk27.literals_free) PV_CBM_CellChunk28.literals_free) PV_CBM_CellChunk29.literals_free) PV_CBM_CellChunk30.literals_free) PV_CBM_CellChunk31.literals_free) PV_CBM_CellChunk32.literals_free) PV_CBM_CellChunk33.literals_free) PV_CBM_CellChunk34.literals_free) PV_CBM_CellChunk35.literals_free) PV_CBM_CellChunk36.literals_free) PV_CBM_CellChunk37.literals_free) PV_CBM_CellChunk38.literals_free) PV_CBM_CellChunk39.literals_free) PV_CBM_CellChunk40.literals_free) PV_CBM_CellChunk41.literals_free) PV_CBM_CellChunk42.literals_free) PV_CBM_CellChunk43.literals_free) PV_CBM_CellChunk44.literals_free) PV_CBM_CellChunk45.literals_free) PV_CBM_CellChunk46.literals_free) PV_CBM_CellChunk47.literals_free) PV_CBM_CellChunk48.literals_free) PV_CBM_CellChunk49.literals_free) PV_CBM_CellChunk50.literals_free) PV_CBM_CellChunk51.literals_free) PV_CBM_CellChunk52.literals_free) PV_CBM_CellChunk53.literals_free) PV_CBM_CellChunk54.literals_free) PV_CBM_CellChunk55.literals_free) PV_CBM_CellChunk56.literals_free) PV_CBM_CellChunk57.literals_free) PV_CBM_CellChunk58.literals_free) PV_CBM_CellChunk59.literals_free
theorem fill (out : alloc.vec.Vec Cell) (hc : out.val.length+3803≤4096) :
  ∃ result, PV_CBM_CellsRaw.reference.fill_cells out = ok (.Ok (), result) ∧ result.val = out.val ++ literals := by
  have hl0 : out.val.length = out.val.length + 0 := (Nat.add_zero _).symm
  obtain ⟨out1,h1,hv1⟩ := PV_CBM_CellChunk00.run out (PV_CBM_ListComposition.capacity_step hc hl0 (by decide))
  have hl1 : out1.val.length = out.val.length+64 :=
    PV_CBM_ListComposition.length_step hv1 PV_CBM_CellChunk00.length hl0
  obtain ⟨out2,h2,hv2⟩ := PV_CBM_CellChunk01.run out1 (PV_CBM_ListComposition.capacity_step hc hl1 (by decide))
  have hl2 : out2.val.length = out.val.length+128 :=
    PV_CBM_ListComposition.length_step hv2 PV_CBM_CellChunk01.length hl1
  obtain ⟨out3,h3,hv3⟩ := PV_CBM_CellChunk02.run out2 (PV_CBM_ListComposition.capacity_step hc hl2 (by decide))
  have hl3 : out3.val.length = out.val.length+192 :=
    PV_CBM_ListComposition.length_step hv3 PV_CBM_CellChunk02.length hl2
  obtain ⟨out4,h4,hv4⟩ := PV_CBM_CellChunk03.run out3 (PV_CBM_ListComposition.capacity_step hc hl3 (by decide))
  have hl4 : out4.val.length = out.val.length+256 :=
    PV_CBM_ListComposition.length_step hv4 PV_CBM_CellChunk03.length hl3
  obtain ⟨out5,h5,hv5⟩ := PV_CBM_CellChunk04.run out4 (PV_CBM_ListComposition.capacity_step hc hl4 (by decide))
  have hl5 : out5.val.length = out.val.length+320 :=
    PV_CBM_ListComposition.length_step hv5 PV_CBM_CellChunk04.length hl4
  obtain ⟨out6,h6,hv6⟩ := PV_CBM_CellChunk05.run out5 (PV_CBM_ListComposition.capacity_step hc hl5 (by decide))
  have hl6 : out6.val.length = out.val.length+384 :=
    PV_CBM_ListComposition.length_step hv6 PV_CBM_CellChunk05.length hl5
  obtain ⟨out7,h7,hv7⟩ := PV_CBM_CellChunk06.run out6 (PV_CBM_ListComposition.capacity_step hc hl6 (by decide))
  have hl7 : out7.val.length = out.val.length+448 :=
    PV_CBM_ListComposition.length_step hv7 PV_CBM_CellChunk06.length hl6
  obtain ⟨out8,h8,hv8⟩ := PV_CBM_CellChunk07.run out7 (PV_CBM_ListComposition.capacity_step hc hl7 (by decide))
  have hl8 : out8.val.length = out.val.length+512 :=
    PV_CBM_ListComposition.length_step hv8 PV_CBM_CellChunk07.length hl7
  obtain ⟨out9,h9,hv9⟩ := PV_CBM_CellChunk08.run out8 (PV_CBM_ListComposition.capacity_step hc hl8 (by decide))
  have hl9 : out9.val.length = out.val.length+576 :=
    PV_CBM_ListComposition.length_step hv9 PV_CBM_CellChunk08.length hl8
  obtain ⟨out10,h10,hv10⟩ := PV_CBM_CellChunk09.run out9 (PV_CBM_ListComposition.capacity_step hc hl9 (by decide))
  have hl10 : out10.val.length = out.val.length+640 :=
    PV_CBM_ListComposition.length_step hv10 PV_CBM_CellChunk09.length hl9
  obtain ⟨out11,h11,hv11⟩ := PV_CBM_CellChunk10.run out10 (PV_CBM_ListComposition.capacity_step hc hl10 (by decide))
  have hl11 : out11.val.length = out.val.length+704 :=
    PV_CBM_ListComposition.length_step hv11 PV_CBM_CellChunk10.length hl10
  obtain ⟨out12,h12,hv12⟩ := PV_CBM_CellChunk11.run out11 (PV_CBM_ListComposition.capacity_step hc hl11 (by decide))
  have hl12 : out12.val.length = out.val.length+768 :=
    PV_CBM_ListComposition.length_step hv12 PV_CBM_CellChunk11.length hl11
  obtain ⟨out13,h13,hv13⟩ := PV_CBM_CellChunk12.run out12 (PV_CBM_ListComposition.capacity_step hc hl12 (by decide))
  have hl13 : out13.val.length = out.val.length+832 :=
    PV_CBM_ListComposition.length_step hv13 PV_CBM_CellChunk12.length hl12
  obtain ⟨out14,h14,hv14⟩ := PV_CBM_CellChunk13.run out13 (PV_CBM_ListComposition.capacity_step hc hl13 (by decide))
  have hl14 : out14.val.length = out.val.length+896 :=
    PV_CBM_ListComposition.length_step hv14 PV_CBM_CellChunk13.length hl13
  obtain ⟨out15,h15,hv15⟩ := PV_CBM_CellChunk14.run out14 (PV_CBM_ListComposition.capacity_step hc hl14 (by decide))
  have hl15 : out15.val.length = out.val.length+960 :=
    PV_CBM_ListComposition.length_step hv15 PV_CBM_CellChunk14.length hl14
  obtain ⟨out16,h16,hv16⟩ := PV_CBM_CellChunk15.run out15 (PV_CBM_ListComposition.capacity_step hc hl15 (by decide))
  have hl16 : out16.val.length = out.val.length+1024 :=
    PV_CBM_ListComposition.length_step hv16 PV_CBM_CellChunk15.length hl15
  obtain ⟨out17,h17,hv17⟩ := PV_CBM_CellChunk16.run out16 (PV_CBM_ListComposition.capacity_step hc hl16 (by decide))
  have hl17 : out17.val.length = out.val.length+1088 :=
    PV_CBM_ListComposition.length_step hv17 PV_CBM_CellChunk16.length hl16
  obtain ⟨out18,h18,hv18⟩ := PV_CBM_CellChunk17.run out17 (PV_CBM_ListComposition.capacity_step hc hl17 (by decide))
  have hl18 : out18.val.length = out.val.length+1152 :=
    PV_CBM_ListComposition.length_step hv18 PV_CBM_CellChunk17.length hl17
  obtain ⟨out19,h19,hv19⟩ := PV_CBM_CellChunk18.run out18 (PV_CBM_ListComposition.capacity_step hc hl18 (by decide))
  have hl19 : out19.val.length = out.val.length+1216 :=
    PV_CBM_ListComposition.length_step hv19 PV_CBM_CellChunk18.length hl18
  obtain ⟨out20,h20,hv20⟩ := PV_CBM_CellChunk19.run out19 (PV_CBM_ListComposition.capacity_step hc hl19 (by decide))
  have hl20 : out20.val.length = out.val.length+1280 :=
    PV_CBM_ListComposition.length_step hv20 PV_CBM_CellChunk19.length hl19
  obtain ⟨out21,h21,hv21⟩ := PV_CBM_CellChunk20.run out20 (PV_CBM_ListComposition.capacity_step hc hl20 (by decide))
  have hl21 : out21.val.length = out.val.length+1344 :=
    PV_CBM_ListComposition.length_step hv21 PV_CBM_CellChunk20.length hl20
  obtain ⟨out22,h22,hv22⟩ := PV_CBM_CellChunk21.run out21 (PV_CBM_ListComposition.capacity_step hc hl21 (by decide))
  have hl22 : out22.val.length = out.val.length+1408 :=
    PV_CBM_ListComposition.length_step hv22 PV_CBM_CellChunk21.length hl21
  obtain ⟨out23,h23,hv23⟩ := PV_CBM_CellChunk22.run out22 (PV_CBM_ListComposition.capacity_step hc hl22 (by decide))
  have hl23 : out23.val.length = out.val.length+1472 :=
    PV_CBM_ListComposition.length_step hv23 PV_CBM_CellChunk22.length hl22
  obtain ⟨out24,h24,hv24⟩ := PV_CBM_CellChunk23.run out23 (PV_CBM_ListComposition.capacity_step hc hl23 (by decide))
  have hl24 : out24.val.length = out.val.length+1536 :=
    PV_CBM_ListComposition.length_step hv24 PV_CBM_CellChunk23.length hl23
  obtain ⟨out25,h25,hv25⟩ := PV_CBM_CellChunk24.run out24 (PV_CBM_ListComposition.capacity_step hc hl24 (by decide))
  have hl25 : out25.val.length = out.val.length+1600 :=
    PV_CBM_ListComposition.length_step hv25 PV_CBM_CellChunk24.length hl24
  obtain ⟨out26,h26,hv26⟩ := PV_CBM_CellChunk25.run out25 (PV_CBM_ListComposition.capacity_step hc hl25 (by decide))
  have hl26 : out26.val.length = out.val.length+1664 :=
    PV_CBM_ListComposition.length_step hv26 PV_CBM_CellChunk25.length hl25
  obtain ⟨out27,h27,hv27⟩ := PV_CBM_CellChunk26.run out26 (PV_CBM_ListComposition.capacity_step hc hl26 (by decide))
  have hl27 : out27.val.length = out.val.length+1728 :=
    PV_CBM_ListComposition.length_step hv27 PV_CBM_CellChunk26.length hl26
  obtain ⟨out28,h28,hv28⟩ := PV_CBM_CellChunk27.run out27 (PV_CBM_ListComposition.capacity_step hc hl27 (by decide))
  have hl28 : out28.val.length = out.val.length+1792 :=
    PV_CBM_ListComposition.length_step hv28 PV_CBM_CellChunk27.length hl27
  obtain ⟨out29,h29,hv29⟩ := PV_CBM_CellChunk28.run out28 (PV_CBM_ListComposition.capacity_step hc hl28 (by decide))
  have hl29 : out29.val.length = out.val.length+1856 :=
    PV_CBM_ListComposition.length_step hv29 PV_CBM_CellChunk28.length hl28
  obtain ⟨out30,h30,hv30⟩ := PV_CBM_CellChunk29.run out29 (PV_CBM_ListComposition.capacity_step hc hl29 (by decide))
  have hl30 : out30.val.length = out.val.length+1920 :=
    PV_CBM_ListComposition.length_step hv30 PV_CBM_CellChunk29.length hl29
  obtain ⟨out31,h31,hv31⟩ := PV_CBM_CellChunk30.run out30 (PV_CBM_ListComposition.capacity_step hc hl30 (by decide))
  have hl31 : out31.val.length = out.val.length+1984 :=
    PV_CBM_ListComposition.length_step hv31 PV_CBM_CellChunk30.length hl30
  obtain ⟨out32,h32,hv32⟩ := PV_CBM_CellChunk31.run out31 (PV_CBM_ListComposition.capacity_step hc hl31 (by decide))
  have hl32 : out32.val.length = out.val.length+2048 :=
    PV_CBM_ListComposition.length_step hv32 PV_CBM_CellChunk31.length hl31
  obtain ⟨out33,h33,hv33⟩ := PV_CBM_CellChunk32.run out32 (PV_CBM_ListComposition.capacity_step hc hl32 (by decide))
  have hl33 : out33.val.length = out.val.length+2112 :=
    PV_CBM_ListComposition.length_step hv33 PV_CBM_CellChunk32.length hl32
  obtain ⟨out34,h34,hv34⟩ := PV_CBM_CellChunk33.run out33 (PV_CBM_ListComposition.capacity_step hc hl33 (by decide))
  have hl34 : out34.val.length = out.val.length+2176 :=
    PV_CBM_ListComposition.length_step hv34 PV_CBM_CellChunk33.length hl33
  obtain ⟨out35,h35,hv35⟩ := PV_CBM_CellChunk34.run out34 (PV_CBM_ListComposition.capacity_step hc hl34 (by decide))
  have hl35 : out35.val.length = out.val.length+2240 :=
    PV_CBM_ListComposition.length_step hv35 PV_CBM_CellChunk34.length hl34
  obtain ⟨out36,h36,hv36⟩ := PV_CBM_CellChunk35.run out35 (PV_CBM_ListComposition.capacity_step hc hl35 (by decide))
  have hl36 : out36.val.length = out.val.length+2304 :=
    PV_CBM_ListComposition.length_step hv36 PV_CBM_CellChunk35.length hl35
  obtain ⟨out37,h37,hv37⟩ := PV_CBM_CellChunk36.run out36 (PV_CBM_ListComposition.capacity_step hc hl36 (by decide))
  have hl37 : out37.val.length = out.val.length+2368 :=
    PV_CBM_ListComposition.length_step hv37 PV_CBM_CellChunk36.length hl36
  obtain ⟨out38,h38,hv38⟩ := PV_CBM_CellChunk37.run out37 (PV_CBM_ListComposition.capacity_step hc hl37 (by decide))
  have hl38 : out38.val.length = out.val.length+2432 :=
    PV_CBM_ListComposition.length_step hv38 PV_CBM_CellChunk37.length hl37
  obtain ⟨out39,h39,hv39⟩ := PV_CBM_CellChunk38.run out38 (PV_CBM_ListComposition.capacity_step hc hl38 (by decide))
  have hl39 : out39.val.length = out.val.length+2496 :=
    PV_CBM_ListComposition.length_step hv39 PV_CBM_CellChunk38.length hl38
  obtain ⟨out40,h40,hv40⟩ := PV_CBM_CellChunk39.run out39 (PV_CBM_ListComposition.capacity_step hc hl39 (by decide))
  have hl40 : out40.val.length = out.val.length+2560 :=
    PV_CBM_ListComposition.length_step hv40 PV_CBM_CellChunk39.length hl39
  obtain ⟨out41,h41,hv41⟩ := PV_CBM_CellChunk40.run out40 (PV_CBM_ListComposition.capacity_step hc hl40 (by decide))
  have hl41 : out41.val.length = out.val.length+2624 :=
    PV_CBM_ListComposition.length_step hv41 PV_CBM_CellChunk40.length hl40
  obtain ⟨out42,h42,hv42⟩ := PV_CBM_CellChunk41.run out41 (PV_CBM_ListComposition.capacity_step hc hl41 (by decide))
  have hl42 : out42.val.length = out.val.length+2688 :=
    PV_CBM_ListComposition.length_step hv42 PV_CBM_CellChunk41.length hl41
  obtain ⟨out43,h43,hv43⟩ := PV_CBM_CellChunk42.run out42 (PV_CBM_ListComposition.capacity_step hc hl42 (by decide))
  have hl43 : out43.val.length = out.val.length+2752 :=
    PV_CBM_ListComposition.length_step hv43 PV_CBM_CellChunk42.length hl42
  obtain ⟨out44,h44,hv44⟩ := PV_CBM_CellChunk43.run out43 (PV_CBM_ListComposition.capacity_step hc hl43 (by decide))
  have hl44 : out44.val.length = out.val.length+2816 :=
    PV_CBM_ListComposition.length_step hv44 PV_CBM_CellChunk43.length hl43
  obtain ⟨out45,h45,hv45⟩ := PV_CBM_CellChunk44.run out44 (PV_CBM_ListComposition.capacity_step hc hl44 (by decide))
  have hl45 : out45.val.length = out.val.length+2880 :=
    PV_CBM_ListComposition.length_step hv45 PV_CBM_CellChunk44.length hl44
  obtain ⟨out46,h46,hv46⟩ := PV_CBM_CellChunk45.run out45 (PV_CBM_ListComposition.capacity_step hc hl45 (by decide))
  have hl46 : out46.val.length = out.val.length+2944 :=
    PV_CBM_ListComposition.length_step hv46 PV_CBM_CellChunk45.length hl45
  obtain ⟨out47,h47,hv47⟩ := PV_CBM_CellChunk46.run out46 (PV_CBM_ListComposition.capacity_step hc hl46 (by decide))
  have hl47 : out47.val.length = out.val.length+3008 :=
    PV_CBM_ListComposition.length_step hv47 PV_CBM_CellChunk46.length hl46
  obtain ⟨out48,h48,hv48⟩ := PV_CBM_CellChunk47.run out47 (PV_CBM_ListComposition.capacity_step hc hl47 (by decide))
  have hl48 : out48.val.length = out.val.length+3072 :=
    PV_CBM_ListComposition.length_step hv48 PV_CBM_CellChunk47.length hl47
  obtain ⟨out49,h49,hv49⟩ := PV_CBM_CellChunk48.run out48 (PV_CBM_ListComposition.capacity_step hc hl48 (by decide))
  have hl49 : out49.val.length = out.val.length+3136 :=
    PV_CBM_ListComposition.length_step hv49 PV_CBM_CellChunk48.length hl48
  obtain ⟨out50,h50,hv50⟩ := PV_CBM_CellChunk49.run out49 (PV_CBM_ListComposition.capacity_step hc hl49 (by decide))
  have hl50 : out50.val.length = out.val.length+3200 :=
    PV_CBM_ListComposition.length_step hv50 PV_CBM_CellChunk49.length hl49
  obtain ⟨out51,h51,hv51⟩ := PV_CBM_CellChunk50.run out50 (PV_CBM_ListComposition.capacity_step hc hl50 (by decide))
  have hl51 : out51.val.length = out.val.length+3264 :=
    PV_CBM_ListComposition.length_step hv51 PV_CBM_CellChunk50.length hl50
  obtain ⟨out52,h52,hv52⟩ := PV_CBM_CellChunk51.run out51 (PV_CBM_ListComposition.capacity_step hc hl51 (by decide))
  have hl52 : out52.val.length = out.val.length+3328 :=
    PV_CBM_ListComposition.length_step hv52 PV_CBM_CellChunk51.length hl51
  obtain ⟨out53,h53,hv53⟩ := PV_CBM_CellChunk52.run out52 (PV_CBM_ListComposition.capacity_step hc hl52 (by decide))
  have hl53 : out53.val.length = out.val.length+3392 :=
    PV_CBM_ListComposition.length_step hv53 PV_CBM_CellChunk52.length hl52
  obtain ⟨out54,h54,hv54⟩ := PV_CBM_CellChunk53.run out53 (PV_CBM_ListComposition.capacity_step hc hl53 (by decide))
  have hl54 : out54.val.length = out.val.length+3456 :=
    PV_CBM_ListComposition.length_step hv54 PV_CBM_CellChunk53.length hl53
  obtain ⟨out55,h55,hv55⟩ := PV_CBM_CellChunk54.run out54 (PV_CBM_ListComposition.capacity_step hc hl54 (by decide))
  have hl55 : out55.val.length = out.val.length+3520 :=
    PV_CBM_ListComposition.length_step hv55 PV_CBM_CellChunk54.length hl54
  obtain ⟨out56,h56,hv56⟩ := PV_CBM_CellChunk55.run out55 (PV_CBM_ListComposition.capacity_step hc hl55 (by decide))
  have hl56 : out56.val.length = out.val.length+3584 :=
    PV_CBM_ListComposition.length_step hv56 PV_CBM_CellChunk55.length hl55
  obtain ⟨out57,h57,hv57⟩ := PV_CBM_CellChunk56.run out56 (PV_CBM_ListComposition.capacity_step hc hl56 (by decide))
  have hl57 : out57.val.length = out.val.length+3648 :=
    PV_CBM_ListComposition.length_step hv57 PV_CBM_CellChunk56.length hl56
  obtain ⟨out58,h58,hv58⟩ := PV_CBM_CellChunk57.run out57 (PV_CBM_ListComposition.capacity_step hc hl57 (by decide))
  have hl58 : out58.val.length = out.val.length+3712 :=
    PV_CBM_ListComposition.length_step hv58 PV_CBM_CellChunk57.length hl57
  obtain ⟨out59,h59,hv59⟩ := PV_CBM_CellChunk58.run out58 (PV_CBM_ListComposition.capacity_step hc hl58 (by decide))
  have hl59 : out59.val.length = out.val.length+3776 :=
    PV_CBM_ListComposition.length_step hv59 PV_CBM_CellChunk58.length hl58
  obtain ⟨out60,h60,hv60⟩ := PV_CBM_CellChunk59.run out59 (PV_CBM_ListComposition.capacity_step hc hl59 (by decide))
  have hl60 : out60.val.length = out.val.length+3803 :=
    PV_CBM_ListComposition.length_step hv60 PV_CBM_CellChunk59.length hl59
  refine ⟨out60,?_,?_⟩
  · unfold PV_CBM_CellsRaw.reference.fill_cells
    rw [h1]
    simp only [bind_tc_ok]
    rw [h2]
    simp only [bind_tc_ok]
    rw [h3]
    simp only [bind_tc_ok]
    rw [h4]
    simp only [bind_tc_ok]
    rw [h5]
    simp only [bind_tc_ok]
    rw [h6]
    simp only [bind_tc_ok]
    rw [h7]
    simp only [bind_tc_ok]
    rw [h8]
    simp only [bind_tc_ok]
    rw [h9]
    simp only [bind_tc_ok]
    rw [h10]
    simp only [bind_tc_ok]
    rw [h11]
    simp only [bind_tc_ok]
    rw [h12]
    simp only [bind_tc_ok]
    rw [h13]
    simp only [bind_tc_ok]
    rw [h14]
    simp only [bind_tc_ok]
    rw [h15]
    simp only [bind_tc_ok]
    rw [h16]
    simp only [bind_tc_ok]
    rw [h17]
    simp only [bind_tc_ok]
    rw [h18]
    simp only [bind_tc_ok]
    rw [h19]
    simp only [bind_tc_ok]
    rw [h20]
    simp only [bind_tc_ok]
    rw [h21]
    simp only [bind_tc_ok]
    rw [h22]
    simp only [bind_tc_ok]
    rw [h23]
    simp only [bind_tc_ok]
    rw [h24]
    simp only [bind_tc_ok]
    rw [h25]
    simp only [bind_tc_ok]
    rw [h26]
    simp only [bind_tc_ok]
    rw [h27]
    simp only [bind_tc_ok]
    rw [h28]
    simp only [bind_tc_ok]
    rw [h29]
    simp only [bind_tc_ok]
    rw [h30]
    simp only [bind_tc_ok]
    rw [h31]
    simp only [bind_tc_ok]
    rw [h32]
    simp only [bind_tc_ok]
    rw [h33]
    simp only [bind_tc_ok]
    rw [h34]
    simp only [bind_tc_ok]
    rw [h35]
    simp only [bind_tc_ok]
    rw [h36]
    simp only [bind_tc_ok]
    rw [h37]
    simp only [bind_tc_ok]
    rw [h38]
    simp only [bind_tc_ok]
    rw [h39]
    simp only [bind_tc_ok]
    rw [h40]
    simp only [bind_tc_ok]
    rw [h41]
    simp only [bind_tc_ok]
    rw [h42]
    simp only [bind_tc_ok]
    rw [h43]
    simp only [bind_tc_ok]
    rw [h44]
    simp only [bind_tc_ok]
    rw [h45]
    simp only [bind_tc_ok]
    rw [h46]
    simp only [bind_tc_ok]
    rw [h47]
    simp only [bind_tc_ok]
    rw [h48]
    simp only [bind_tc_ok]
    rw [h49]
    simp only [bind_tc_ok]
    rw [h50]
    simp only [bind_tc_ok]
    rw [h51]
    simp only [bind_tc_ok]
    rw [h52]
    simp only [bind_tc_ok]
    rw [h53]
    simp only [bind_tc_ok]
    rw [h54]
    simp only [bind_tc_ok]
    rw [h55]
    simp only [bind_tc_ok]
    rw [h56]
    simp only [bind_tc_ok]
    rw [h57]
    simp only [bind_tc_ok]
    rw [h58]
    simp only [bind_tc_ok]
    rw [h59]
    simp only [bind_tc_ok]
    rw [h60]
    simp only [bind_tc_ok]
  · rw [hv60,hv59,hv58,hv57,hv56,hv55,hv54,hv53,hv52,hv51,hv50,hv49,hv48,hv47,hv46,hv45,hv44,hv43,hv42,hv41,hv40,hv39,hv38,hv37,hv36,hv35,hv34,hv33,hv32,hv31,hv30,hv29,hv28,hv27,hv26,hv25,hv24,hv23,hv22,hv21,hv20,hv19,hv18,hv17,hv16,hv15,hv14,hv13,hv12,hv11,hv10,hv9,hv8,hv7,hv6,hv5,hv4,hv3,hv2,hv1]
    simp only [literals,List.append_assoc]
theorem callback : ∃ result : alloc.vec.Vec Cell,
    PV_CBM_CellsMaterializer.callback = ok (.Ok result) ∧
    result.val.length = 3803 ∧
    (∀ cell ∈ result.val, PV_CBM_InventoryShape.free cell.row.val cell.column.val) := by
  obtain ⟨result,hr,hv⟩ := fill (alloc.vec.Vec.new Cell) (by change 0+3803≤4096; decide)
  have he : result.val = literals := by simpa only [alloc.vec.Vec.new,List.nil_append] using hv
  refine ⟨result,?_,?_,?_⟩
  · unfold PV_CBM_CellsMaterializer.callback
    rw [hr]
    exact PV_CBM_CellsMaterializer.snapshot_ok result
  · rw [he,length]
  · rw [he]
    exact all_free
#print axioms length
#print axioms all_free
#print axioms fill
#print axioms callback
end R1Z.PV_CBM_CellsSpec
