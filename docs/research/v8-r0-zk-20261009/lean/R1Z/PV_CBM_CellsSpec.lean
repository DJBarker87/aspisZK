import R1Z.PV_CBM_CellsMaterializer
namespace R1Z.PV_CBM_CellsSpec
open Aeneas Aeneas.Std Result
set_option autoImplicit false
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
  intro cell hc
  simp only [literals,List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59
  · exact PV_CBM_CellChunk00.literals_free cell h0
  · exact PV_CBM_CellChunk01.literals_free cell h1
  · exact PV_CBM_CellChunk02.literals_free cell h2
  · exact PV_CBM_CellChunk03.literals_free cell h3
  · exact PV_CBM_CellChunk04.literals_free cell h4
  · exact PV_CBM_CellChunk05.literals_free cell h5
  · exact PV_CBM_CellChunk06.literals_free cell h6
  · exact PV_CBM_CellChunk07.literals_free cell h7
  · exact PV_CBM_CellChunk08.literals_free cell h8
  · exact PV_CBM_CellChunk09.literals_free cell h9
  · exact PV_CBM_CellChunk10.literals_free cell h10
  · exact PV_CBM_CellChunk11.literals_free cell h11
  · exact PV_CBM_CellChunk12.literals_free cell h12
  · exact PV_CBM_CellChunk13.literals_free cell h13
  · exact PV_CBM_CellChunk14.literals_free cell h14
  · exact PV_CBM_CellChunk15.literals_free cell h15
  · exact PV_CBM_CellChunk16.literals_free cell h16
  · exact PV_CBM_CellChunk17.literals_free cell h17
  · exact PV_CBM_CellChunk18.literals_free cell h18
  · exact PV_CBM_CellChunk19.literals_free cell h19
  · exact PV_CBM_CellChunk20.literals_free cell h20
  · exact PV_CBM_CellChunk21.literals_free cell h21
  · exact PV_CBM_CellChunk22.literals_free cell h22
  · exact PV_CBM_CellChunk23.literals_free cell h23
  · exact PV_CBM_CellChunk24.literals_free cell h24
  · exact PV_CBM_CellChunk25.literals_free cell h25
  · exact PV_CBM_CellChunk26.literals_free cell h26
  · exact PV_CBM_CellChunk27.literals_free cell h27
  · exact PV_CBM_CellChunk28.literals_free cell h28
  · exact PV_CBM_CellChunk29.literals_free cell h29
  · exact PV_CBM_CellChunk30.literals_free cell h30
  · exact PV_CBM_CellChunk31.literals_free cell h31
  · exact PV_CBM_CellChunk32.literals_free cell h32
  · exact PV_CBM_CellChunk33.literals_free cell h33
  · exact PV_CBM_CellChunk34.literals_free cell h34
  · exact PV_CBM_CellChunk35.literals_free cell h35
  · exact PV_CBM_CellChunk36.literals_free cell h36
  · exact PV_CBM_CellChunk37.literals_free cell h37
  · exact PV_CBM_CellChunk38.literals_free cell h38
  · exact PV_CBM_CellChunk39.literals_free cell h39
  · exact PV_CBM_CellChunk40.literals_free cell h40
  · exact PV_CBM_CellChunk41.literals_free cell h41
  · exact PV_CBM_CellChunk42.literals_free cell h42
  · exact PV_CBM_CellChunk43.literals_free cell h43
  · exact PV_CBM_CellChunk44.literals_free cell h44
  · exact PV_CBM_CellChunk45.literals_free cell h45
  · exact PV_CBM_CellChunk46.literals_free cell h46
  · exact PV_CBM_CellChunk47.literals_free cell h47
  · exact PV_CBM_CellChunk48.literals_free cell h48
  · exact PV_CBM_CellChunk49.literals_free cell h49
  · exact PV_CBM_CellChunk50.literals_free cell h50
  · exact PV_CBM_CellChunk51.literals_free cell h51
  · exact PV_CBM_CellChunk52.literals_free cell h52
  · exact PV_CBM_CellChunk53.literals_free cell h53
  · exact PV_CBM_CellChunk54.literals_free cell h54
  · exact PV_CBM_CellChunk55.literals_free cell h55
  · exact PV_CBM_CellChunk56.literals_free cell h56
  · exact PV_CBM_CellChunk57.literals_free cell h57
  · exact PV_CBM_CellChunk58.literals_free cell h58
  · exact PV_CBM_CellChunk59.literals_free cell h59
theorem fill (out : alloc.vec.Vec Cell) (hc : out.val.length+3803≤4096) :
  ∃ result, PV_CBM_CellsRaw.reference.fill_cells out = ok (.Ok (), result) ∧ result.val = out.val ++ literals := by
  obtain ⟨out1,h1,hv1⟩ := PV_CBM_CellChunk00.run out (by omega)
  have hl1 : out1.val.length = out.val.length+64 := by
    rw [hv1,List.length_append,PV_CBM_CellChunk00.length]
    omega
  obtain ⟨out2,h2,hv2⟩ := PV_CBM_CellChunk01.run out1 (by omega)
  have hl2 : out2.val.length = out.val.length+128 := by
    rw [hv2,List.length_append,PV_CBM_CellChunk01.length]
    rw [hl1]
    omega
  obtain ⟨out3,h3,hv3⟩ := PV_CBM_CellChunk02.run out2 (by omega)
  have hl3 : out3.val.length = out.val.length+192 := by
    rw [hv3,List.length_append,PV_CBM_CellChunk02.length]
    rw [hl2]
    omega
  obtain ⟨out4,h4,hv4⟩ := PV_CBM_CellChunk03.run out3 (by omega)
  have hl4 : out4.val.length = out.val.length+256 := by
    rw [hv4,List.length_append,PV_CBM_CellChunk03.length]
    rw [hl3]
    omega
  obtain ⟨out5,h5,hv5⟩ := PV_CBM_CellChunk04.run out4 (by omega)
  have hl5 : out5.val.length = out.val.length+320 := by
    rw [hv5,List.length_append,PV_CBM_CellChunk04.length]
    rw [hl4]
    omega
  obtain ⟨out6,h6,hv6⟩ := PV_CBM_CellChunk05.run out5 (by omega)
  have hl6 : out6.val.length = out.val.length+384 := by
    rw [hv6,List.length_append,PV_CBM_CellChunk05.length]
    rw [hl5]
    omega
  obtain ⟨out7,h7,hv7⟩ := PV_CBM_CellChunk06.run out6 (by omega)
  have hl7 : out7.val.length = out.val.length+448 := by
    rw [hv7,List.length_append,PV_CBM_CellChunk06.length]
    rw [hl6]
    omega
  obtain ⟨out8,h8,hv8⟩ := PV_CBM_CellChunk07.run out7 (by omega)
  have hl8 : out8.val.length = out.val.length+512 := by
    rw [hv8,List.length_append,PV_CBM_CellChunk07.length]
    rw [hl7]
    omega
  obtain ⟨out9,h9,hv9⟩ := PV_CBM_CellChunk08.run out8 (by omega)
  have hl9 : out9.val.length = out.val.length+576 := by
    rw [hv9,List.length_append,PV_CBM_CellChunk08.length]
    rw [hl8]
    omega
  obtain ⟨out10,h10,hv10⟩ := PV_CBM_CellChunk09.run out9 (by omega)
  have hl10 : out10.val.length = out.val.length+640 := by
    rw [hv10,List.length_append,PV_CBM_CellChunk09.length]
    rw [hl9]
    omega
  obtain ⟨out11,h11,hv11⟩ := PV_CBM_CellChunk10.run out10 (by omega)
  have hl11 : out11.val.length = out.val.length+704 := by
    rw [hv11,List.length_append,PV_CBM_CellChunk10.length]
    rw [hl10]
    omega
  obtain ⟨out12,h12,hv12⟩ := PV_CBM_CellChunk11.run out11 (by omega)
  have hl12 : out12.val.length = out.val.length+768 := by
    rw [hv12,List.length_append,PV_CBM_CellChunk11.length]
    rw [hl11]
    omega
  obtain ⟨out13,h13,hv13⟩ := PV_CBM_CellChunk12.run out12 (by omega)
  have hl13 : out13.val.length = out.val.length+832 := by
    rw [hv13,List.length_append,PV_CBM_CellChunk12.length]
    rw [hl12]
    omega
  obtain ⟨out14,h14,hv14⟩ := PV_CBM_CellChunk13.run out13 (by omega)
  have hl14 : out14.val.length = out.val.length+896 := by
    rw [hv14,List.length_append,PV_CBM_CellChunk13.length]
    rw [hl13]
    omega
  obtain ⟨out15,h15,hv15⟩ := PV_CBM_CellChunk14.run out14 (by omega)
  have hl15 : out15.val.length = out.val.length+960 := by
    rw [hv15,List.length_append,PV_CBM_CellChunk14.length]
    rw [hl14]
    omega
  obtain ⟨out16,h16,hv16⟩ := PV_CBM_CellChunk15.run out15 (by omega)
  have hl16 : out16.val.length = out.val.length+1024 := by
    rw [hv16,List.length_append,PV_CBM_CellChunk15.length]
    rw [hl15]
    omega
  obtain ⟨out17,h17,hv17⟩ := PV_CBM_CellChunk16.run out16 (by omega)
  have hl17 : out17.val.length = out.val.length+1088 := by
    rw [hv17,List.length_append,PV_CBM_CellChunk16.length]
    rw [hl16]
    omega
  obtain ⟨out18,h18,hv18⟩ := PV_CBM_CellChunk17.run out17 (by omega)
  have hl18 : out18.val.length = out.val.length+1152 := by
    rw [hv18,List.length_append,PV_CBM_CellChunk17.length]
    rw [hl17]
    omega
  obtain ⟨out19,h19,hv19⟩ := PV_CBM_CellChunk18.run out18 (by omega)
  have hl19 : out19.val.length = out.val.length+1216 := by
    rw [hv19,List.length_append,PV_CBM_CellChunk18.length]
    rw [hl18]
    omega
  obtain ⟨out20,h20,hv20⟩ := PV_CBM_CellChunk19.run out19 (by omega)
  have hl20 : out20.val.length = out.val.length+1280 := by
    rw [hv20,List.length_append,PV_CBM_CellChunk19.length]
    rw [hl19]
    omega
  obtain ⟨out21,h21,hv21⟩ := PV_CBM_CellChunk20.run out20 (by omega)
  have hl21 : out21.val.length = out.val.length+1344 := by
    rw [hv21,List.length_append,PV_CBM_CellChunk20.length]
    rw [hl20]
    omega
  obtain ⟨out22,h22,hv22⟩ := PV_CBM_CellChunk21.run out21 (by omega)
  have hl22 : out22.val.length = out.val.length+1408 := by
    rw [hv22,List.length_append,PV_CBM_CellChunk21.length]
    rw [hl21]
    omega
  obtain ⟨out23,h23,hv23⟩ := PV_CBM_CellChunk22.run out22 (by omega)
  have hl23 : out23.val.length = out.val.length+1472 := by
    rw [hv23,List.length_append,PV_CBM_CellChunk22.length]
    rw [hl22]
    omega
  obtain ⟨out24,h24,hv24⟩ := PV_CBM_CellChunk23.run out23 (by omega)
  have hl24 : out24.val.length = out.val.length+1536 := by
    rw [hv24,List.length_append,PV_CBM_CellChunk23.length]
    rw [hl23]
    omega
  obtain ⟨out25,h25,hv25⟩ := PV_CBM_CellChunk24.run out24 (by omega)
  have hl25 : out25.val.length = out.val.length+1600 := by
    rw [hv25,List.length_append,PV_CBM_CellChunk24.length]
    rw [hl24]
    omega
  obtain ⟨out26,h26,hv26⟩ := PV_CBM_CellChunk25.run out25 (by omega)
  have hl26 : out26.val.length = out.val.length+1664 := by
    rw [hv26,List.length_append,PV_CBM_CellChunk25.length]
    rw [hl25]
    omega
  obtain ⟨out27,h27,hv27⟩ := PV_CBM_CellChunk26.run out26 (by omega)
  have hl27 : out27.val.length = out.val.length+1728 := by
    rw [hv27,List.length_append,PV_CBM_CellChunk26.length]
    rw [hl26]
    omega
  obtain ⟨out28,h28,hv28⟩ := PV_CBM_CellChunk27.run out27 (by omega)
  have hl28 : out28.val.length = out.val.length+1792 := by
    rw [hv28,List.length_append,PV_CBM_CellChunk27.length]
    rw [hl27]
    omega
  obtain ⟨out29,h29,hv29⟩ := PV_CBM_CellChunk28.run out28 (by omega)
  have hl29 : out29.val.length = out.val.length+1856 := by
    rw [hv29,List.length_append,PV_CBM_CellChunk28.length]
    rw [hl28]
    omega
  obtain ⟨out30,h30,hv30⟩ := PV_CBM_CellChunk29.run out29 (by omega)
  have hl30 : out30.val.length = out.val.length+1920 := by
    rw [hv30,List.length_append,PV_CBM_CellChunk29.length]
    rw [hl29]
    omega
  obtain ⟨out31,h31,hv31⟩ := PV_CBM_CellChunk30.run out30 (by omega)
  have hl31 : out31.val.length = out.val.length+1984 := by
    rw [hv31,List.length_append,PV_CBM_CellChunk30.length]
    rw [hl30]
    omega
  obtain ⟨out32,h32,hv32⟩ := PV_CBM_CellChunk31.run out31 (by omega)
  have hl32 : out32.val.length = out.val.length+2048 := by
    rw [hv32,List.length_append,PV_CBM_CellChunk31.length]
    rw [hl31]
    omega
  obtain ⟨out33,h33,hv33⟩ := PV_CBM_CellChunk32.run out32 (by omega)
  have hl33 : out33.val.length = out.val.length+2112 := by
    rw [hv33,List.length_append,PV_CBM_CellChunk32.length]
    rw [hl32]
    omega
  obtain ⟨out34,h34,hv34⟩ := PV_CBM_CellChunk33.run out33 (by omega)
  have hl34 : out34.val.length = out.val.length+2176 := by
    rw [hv34,List.length_append,PV_CBM_CellChunk33.length]
    rw [hl33]
    omega
  obtain ⟨out35,h35,hv35⟩ := PV_CBM_CellChunk34.run out34 (by omega)
  have hl35 : out35.val.length = out.val.length+2240 := by
    rw [hv35,List.length_append,PV_CBM_CellChunk34.length]
    rw [hl34]
    omega
  obtain ⟨out36,h36,hv36⟩ := PV_CBM_CellChunk35.run out35 (by omega)
  have hl36 : out36.val.length = out.val.length+2304 := by
    rw [hv36,List.length_append,PV_CBM_CellChunk35.length]
    rw [hl35]
    omega
  obtain ⟨out37,h37,hv37⟩ := PV_CBM_CellChunk36.run out36 (by omega)
  have hl37 : out37.val.length = out.val.length+2368 := by
    rw [hv37,List.length_append,PV_CBM_CellChunk36.length]
    rw [hl36]
    omega
  obtain ⟨out38,h38,hv38⟩ := PV_CBM_CellChunk37.run out37 (by omega)
  have hl38 : out38.val.length = out.val.length+2432 := by
    rw [hv38,List.length_append,PV_CBM_CellChunk37.length]
    rw [hl37]
    omega
  obtain ⟨out39,h39,hv39⟩ := PV_CBM_CellChunk38.run out38 (by omega)
  have hl39 : out39.val.length = out.val.length+2496 := by
    rw [hv39,List.length_append,PV_CBM_CellChunk38.length]
    rw [hl38]
    omega
  obtain ⟨out40,h40,hv40⟩ := PV_CBM_CellChunk39.run out39 (by omega)
  have hl40 : out40.val.length = out.val.length+2560 := by
    rw [hv40,List.length_append,PV_CBM_CellChunk39.length]
    rw [hl39]
    omega
  obtain ⟨out41,h41,hv41⟩ := PV_CBM_CellChunk40.run out40 (by omega)
  have hl41 : out41.val.length = out.val.length+2624 := by
    rw [hv41,List.length_append,PV_CBM_CellChunk40.length]
    rw [hl40]
    omega
  obtain ⟨out42,h42,hv42⟩ := PV_CBM_CellChunk41.run out41 (by omega)
  have hl42 : out42.val.length = out.val.length+2688 := by
    rw [hv42,List.length_append,PV_CBM_CellChunk41.length]
    rw [hl41]
    omega
  obtain ⟨out43,h43,hv43⟩ := PV_CBM_CellChunk42.run out42 (by omega)
  have hl43 : out43.val.length = out.val.length+2752 := by
    rw [hv43,List.length_append,PV_CBM_CellChunk42.length]
    rw [hl42]
    omega
  obtain ⟨out44,h44,hv44⟩ := PV_CBM_CellChunk43.run out43 (by omega)
  have hl44 : out44.val.length = out.val.length+2816 := by
    rw [hv44,List.length_append,PV_CBM_CellChunk43.length]
    rw [hl43]
    omega
  obtain ⟨out45,h45,hv45⟩ := PV_CBM_CellChunk44.run out44 (by omega)
  have hl45 : out45.val.length = out.val.length+2880 := by
    rw [hv45,List.length_append,PV_CBM_CellChunk44.length]
    rw [hl44]
    omega
  obtain ⟨out46,h46,hv46⟩ := PV_CBM_CellChunk45.run out45 (by omega)
  have hl46 : out46.val.length = out.val.length+2944 := by
    rw [hv46,List.length_append,PV_CBM_CellChunk45.length]
    rw [hl45]
    omega
  obtain ⟨out47,h47,hv47⟩ := PV_CBM_CellChunk46.run out46 (by omega)
  have hl47 : out47.val.length = out.val.length+3008 := by
    rw [hv47,List.length_append,PV_CBM_CellChunk46.length]
    rw [hl46]
    omega
  obtain ⟨out48,h48,hv48⟩ := PV_CBM_CellChunk47.run out47 (by omega)
  have hl48 : out48.val.length = out.val.length+3072 := by
    rw [hv48,List.length_append,PV_CBM_CellChunk47.length]
    rw [hl47]
    omega
  obtain ⟨out49,h49,hv49⟩ := PV_CBM_CellChunk48.run out48 (by omega)
  have hl49 : out49.val.length = out.val.length+3136 := by
    rw [hv49,List.length_append,PV_CBM_CellChunk48.length]
    rw [hl48]
    omega
  obtain ⟨out50,h50,hv50⟩ := PV_CBM_CellChunk49.run out49 (by omega)
  have hl50 : out50.val.length = out.val.length+3200 := by
    rw [hv50,List.length_append,PV_CBM_CellChunk49.length]
    rw [hl49]
    omega
  obtain ⟨out51,h51,hv51⟩ := PV_CBM_CellChunk50.run out50 (by omega)
  have hl51 : out51.val.length = out.val.length+3264 := by
    rw [hv51,List.length_append,PV_CBM_CellChunk50.length]
    rw [hl50]
    omega
  obtain ⟨out52,h52,hv52⟩ := PV_CBM_CellChunk51.run out51 (by omega)
  have hl52 : out52.val.length = out.val.length+3328 := by
    rw [hv52,List.length_append,PV_CBM_CellChunk51.length]
    rw [hl51]
    omega
  obtain ⟨out53,h53,hv53⟩ := PV_CBM_CellChunk52.run out52 (by omega)
  have hl53 : out53.val.length = out.val.length+3392 := by
    rw [hv53,List.length_append,PV_CBM_CellChunk52.length]
    rw [hl52]
    omega
  obtain ⟨out54,h54,hv54⟩ := PV_CBM_CellChunk53.run out53 (by omega)
  have hl54 : out54.val.length = out.val.length+3456 := by
    rw [hv54,List.length_append,PV_CBM_CellChunk53.length]
    rw [hl53]
    omega
  obtain ⟨out55,h55,hv55⟩ := PV_CBM_CellChunk54.run out54 (by omega)
  have hl55 : out55.val.length = out.val.length+3520 := by
    rw [hv55,List.length_append,PV_CBM_CellChunk54.length]
    rw [hl54]
    omega
  obtain ⟨out56,h56,hv56⟩ := PV_CBM_CellChunk55.run out55 (by omega)
  have hl56 : out56.val.length = out.val.length+3584 := by
    rw [hv56,List.length_append,PV_CBM_CellChunk55.length]
    rw [hl55]
    omega
  obtain ⟨out57,h57,hv57⟩ := PV_CBM_CellChunk56.run out56 (by omega)
  have hl57 : out57.val.length = out.val.length+3648 := by
    rw [hv57,List.length_append,PV_CBM_CellChunk56.length]
    rw [hl56]
    omega
  obtain ⟨out58,h58,hv58⟩ := PV_CBM_CellChunk57.run out57 (by omega)
  have hl58 : out58.val.length = out.val.length+3712 := by
    rw [hv58,List.length_append,PV_CBM_CellChunk57.length]
    rw [hl57]
    omega
  obtain ⟨out59,h59,hv59⟩ := PV_CBM_CellChunk58.run out58 (by omega)
  have hl59 : out59.val.length = out.val.length+3776 := by
    rw [hv59,List.length_append,PV_CBM_CellChunk58.length]
    rw [hl58]
    omega
  obtain ⟨out60,h60,hv60⟩ := PV_CBM_CellChunk59.run out59 (by omega)
  have hl60 : out60.val.length = out.val.length+3803 := by
    rw [hv60,List.length_append,PV_CBM_CellChunk59.length]
    rw [hl59]
    omega
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
