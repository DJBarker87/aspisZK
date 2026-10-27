import R1Z.PV_Op134_CellOrder00
import R1Z.PV_Op134_CellOrder01
import R1Z.PV_Op134_CellOrder02
import R1Z.PV_Op134_CellOrder03
import R1Z.PV_Op134_CellOrder04
import R1Z.PV_Op134_CellOrder05
import R1Z.PV_Op134_CellOrder06
import R1Z.PV_Op134_CellOrder07
import R1Z.PV_Op134_CellOrder08
import R1Z.PV_Op134_CellOrder09
import R1Z.PV_Op134_CellOrder10
import R1Z.PV_Op134_CellOrder11
import R1Z.PV_Op134_CellOrder12
import R1Z.PV_Op134_CellOrder13
import R1Z.PV_Op134_CellOrder14
import R1Z.PV_Op134_CellOrder15
import R1Z.PV_Op134_CellOrder16
import R1Z.PV_Op134_CellOrder17
import R1Z.PV_Op134_CellOrder18
import R1Z.PV_Op134_CellOrder19
import R1Z.PV_Op134_CellOrder20
import R1Z.PV_Op134_CellOrder21
import R1Z.PV_Op134_CellOrder22
import R1Z.PV_Op134_CellOrder23
import R1Z.PV_Op134_CellOrder24
import R1Z.PV_Op134_CellOrder25
import R1Z.PV_Op134_CellOrder26
import R1Z.PV_Op134_CellOrder27
import R1Z.PV_Op134_CellOrder28
import R1Z.PV_Op134_CellOrder29
import R1Z.PV_Op134_CellOrder30
import R1Z.PV_Op134_CellOrder31
import R1Z.PV_Op134_CellOrder32
import R1Z.PV_Op134_CellOrder33
import R1Z.PV_Op134_CellOrder34
import R1Z.PV_Op134_CellOrder35
import R1Z.PV_Op134_CellOrder36
import R1Z.PV_Op134_CellOrder37
import R1Z.PV_Op134_CellOrder38
import R1Z.PV_Op134_CellOrder39
import R1Z.PV_Op134_CellOrder40
import R1Z.PV_Op134_CellOrder41
import R1Z.PV_Op134_CellOrder42
import R1Z.PV_Op134_CellOrder43
import R1Z.PV_Op134_CellOrder44
import R1Z.PV_Op134_CellOrder45
import R1Z.PV_Op134_CellOrder46
import R1Z.PV_Op134_CellOrder47
import R1Z.PV_Op134_CellOrder48
import R1Z.PV_Op134_CellOrder49
import R1Z.PV_Op134_CellOrder50
import R1Z.PV_Op134_CellOrder51
import R1Z.PV_Op134_CellOrder52
import R1Z.PV_Op134_CellOrder53
import R1Z.PV_Op134_CellOrder54
import R1Z.PV_Op134_CellOrder55
import R1Z.PV_Op134_CellOrder56
import R1Z.PV_Op134_CellOrder57
import R1Z.PV_Op134_CellOrder58
import R1Z.PV_Op134_CellOrder59
import R1Z.PV_CBM_CellsSpec
import R1Z.PV_Op134_Coverage
namespace R1Z.PV_Op134_Inventory
open PV_Op134_Order
set_option autoImplicit false
attribute [local irreducible] PV_CBM_CellChunk00.literals PV_CBM_CellChunk01.literals PV_CBM_CellChunk02.literals PV_CBM_CellChunk03.literals PV_CBM_CellChunk04.literals PV_CBM_CellChunk05.literals PV_CBM_CellChunk06.literals PV_CBM_CellChunk07.literals PV_CBM_CellChunk08.literals PV_CBM_CellChunk09.literals PV_CBM_CellChunk10.literals PV_CBM_CellChunk11.literals PV_CBM_CellChunk12.literals PV_CBM_CellChunk13.literals PV_CBM_CellChunk14.literals PV_CBM_CellChunk15.literals PV_CBM_CellChunk16.literals PV_CBM_CellChunk17.literals PV_CBM_CellChunk18.literals PV_CBM_CellChunk19.literals PV_CBM_CellChunk20.literals PV_CBM_CellChunk21.literals PV_CBM_CellChunk22.literals PV_CBM_CellChunk23.literals PV_CBM_CellChunk24.literals PV_CBM_CellChunk25.literals PV_CBM_CellChunk26.literals PV_CBM_CellChunk27.literals PV_CBM_CellChunk28.literals PV_CBM_CellChunk29.literals PV_CBM_CellChunk30.literals PV_CBM_CellChunk31.literals PV_CBM_CellChunk32.literals PV_CBM_CellChunk33.literals PV_CBM_CellChunk34.literals PV_CBM_CellChunk35.literals PV_CBM_CellChunk36.literals PV_CBM_CellChunk37.literals PV_CBM_CellChunk38.literals PV_CBM_CellChunk39.literals PV_CBM_CellChunk40.literals PV_CBM_CellChunk41.literals PV_CBM_CellChunk42.literals PV_CBM_CellChunk43.literals PV_CBM_CellChunk44.literals PV_CBM_CellChunk45.literals PV_CBM_CellChunk46.literals PV_CBM_CellChunk47.literals PV_CBM_CellChunk48.literals PV_CBM_CellChunk49.literals PV_CBM_CellChunk50.literals PV_CBM_CellChunk51.literals PV_CBM_CellChunk52.literals PV_CBM_CellChunk53.literals PV_CBM_CellChunk54.literals PV_CBM_CellChunk55.literals PV_CBM_CellChunk56.literals PV_CBM_CellChunk57.literals PV_CBM_CellChunk58.literals PV_CBM_CellChunk59.literals
theorem ordered_bounds : increasing PV_CBM_CellsSpec.literals ∧
    ∀ c ∈ PV_CBM_CellsSpec.literals, 13 ≤ key c ∧ key c < 16384 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
  have b0 : increasing PV_CBM_CellChunk00.literals ∧ ∀ c ∈ PV_CBM_CellChunk00.literals, 13 ≤ key c ∧ key c < 350 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder00.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder00.bounds c hc
    omega
  have b1 : increasing PV_CBM_CellChunk01.literals ∧ ∀ c ∈ PV_CBM_CellChunk01.literals, 350 ≤ key c ∧ key c < 687 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder01.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder01.bounds c hc
    omega
  have b2 : increasing PV_CBM_CellChunk02.literals ∧ ∀ c ∈ PV_CBM_CellChunk02.literals, 687 ≤ key c ∧ key c < 955 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder02.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder02.bounds c hc
    omega
  have b3 : increasing PV_CBM_CellChunk03.literals ∧ ∀ c ∈ PV_CBM_CellChunk03.literals, 955 ≤ key c ∧ key c < 1214 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder03.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder03.bounds c hc
    omega
  have b4 : increasing PV_CBM_CellChunk04.literals ∧ ∀ c ∈ PV_CBM_CellChunk04.literals, 1214 ≤ key c ∧ key c < 1551 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder04.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder04.bounds c hc
    omega
  have b5 : increasing PV_CBM_CellChunk05.literals ∧ ∀ c ∈ PV_CBM_CellChunk05.literals, 1551 ≤ key c ∧ key c < 1901 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder05.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder05.bounds c hc
    omega
  have b6 : increasing PV_CBM_CellChunk06.literals ∧ ∀ c ∈ PV_CBM_CellChunk06.literals, 1901 ≤ key c ∧ key c < 2078 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder06.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder06.bounds c hc
    omega
  have b7 : increasing PV_CBM_CellChunk07.literals ∧ ∀ c ∈ PV_CBM_CellChunk07.literals, 2078 ≤ key c ∧ key c < 2415 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder07.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder07.bounds c hc
    omega
  have b8 : increasing PV_CBM_CellChunk08.literals ∧ ∀ c ∈ PV_CBM_CellChunk08.literals, 2415 ≤ key c ∧ key c < 2765 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder08.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder08.bounds c hc
    omega
  have b9 : increasing PV_CBM_CellChunk09.literals ∧ ∀ c ∈ PV_CBM_CellChunk09.literals, 2765 ≤ key c ∧ key c < 3011 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder09.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder09.bounds c hc
    omega
  have b10 : increasing PV_CBM_CellChunk10.literals ∧ ∀ c ∈ PV_CBM_CellChunk10.literals, 3011 ≤ key c ∧ key c < 3278 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder10.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder10.bounds c hc
    omega
  have b11 : increasing PV_CBM_CellChunk11.literals ∧ ∀ c ∈ PV_CBM_CellChunk11.literals, 3278 ≤ key c ∧ key c < 3615 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder11.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder11.bounds c hc
    omega
  have b12 : increasing PV_CBM_CellChunk12.literals ∧ ∀ c ∈ PV_CBM_CellChunk12.literals, 3615 ≤ key c ∧ key c < 3965 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder12.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder12.bounds c hc
    omega
  have b13 : increasing PV_CBM_CellChunk13.literals ∧ ∀ c ∈ PV_CBM_CellChunk13.literals, 3965 ≤ key c ∧ key c < 4127 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder13.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder13.bounds c hc
    omega
  have b14 : increasing PV_CBM_CellChunk14.literals ∧ ∀ c ∈ PV_CBM_CellChunk14.literals, 4127 ≤ key c ∧ key c < 4477 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder14.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder14.bounds c hc
    omega
  have b15 : increasing PV_CBM_CellChunk15.literals ∧ ∀ c ∈ PV_CBM_CellChunk15.literals, 4477 ≤ key c ∧ key c < 4814 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder15.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder15.bounds c hc
    omega
  have b16 : increasing PV_CBM_CellChunk16.literals ∧ ∀ c ∈ PV_CBM_CellChunk16.literals, 4814 ≤ key c ∧ key c < 5060 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder16.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder16.bounds c hc
    omega
  have b17 : increasing PV_CBM_CellChunk17.literals ∧ ∀ c ∈ PV_CBM_CellChunk17.literals, 5060 ≤ key c ∧ key c < 5326 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder17.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder17.bounds c hc
    omega
  have b18 : increasing PV_CBM_CellChunk18.literals ∧ ∀ c ∈ PV_CBM_CellChunk18.literals, 5326 ≤ key c ∧ key c < 5663 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder18.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder18.bounds c hc
    omega
  have b19 : increasing PV_CBM_CellChunk19.literals ∧ ∀ c ∈ PV_CBM_CellChunk19.literals, 5663 ≤ key c ∧ key c < 6013 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder19.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder19.bounds c hc
    omega
  have b20 : increasing PV_CBM_CellChunk20.literals ∧ ∀ c ∈ PV_CBM_CellChunk20.literals, 6013 ≤ key c ∧ key c < 6175 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder20.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder20.bounds c hc
    omega
  have b21 : increasing PV_CBM_CellChunk21.literals ∧ ∀ c ∈ PV_CBM_CellChunk21.literals, 6175 ≤ key c ∧ key c < 6525 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder21.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder21.bounds c hc
    omega
  have b22 : increasing PV_CBM_CellChunk22.literals ∧ ∀ c ∈ PV_CBM_CellChunk22.literals, 6525 ≤ key c ∧ key c < 6862 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder22.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder22.bounds c hc
    omega
  have b23 : increasing PV_CBM_CellChunk23.literals ∧ ∀ c ∈ PV_CBM_CellChunk23.literals, 6862 ≤ key c ∧ key c < 7108 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder23.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder23.bounds c hc
    omega
  have b24 : increasing PV_CBM_CellChunk24.literals ∧ ∀ c ∈ PV_CBM_CellChunk24.literals, 7108 ≤ key c ∧ key c < 7374 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder24.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder24.bounds c hc
    omega
  have b25 : increasing PV_CBM_CellChunk25.literals ∧ ∀ c ∈ PV_CBM_CellChunk25.literals, 7374 ≤ key c ∧ key c < 7711 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder25.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder25.bounds c hc
    omega
  have b26 : increasing PV_CBM_CellChunk26.literals ∧ ∀ c ∈ PV_CBM_CellChunk26.literals, 7711 ≤ key c ∧ key c < 8061 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder26.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder26.bounds c hc
    omega
  have b27 : increasing PV_CBM_CellChunk27.literals ∧ ∀ c ∈ PV_CBM_CellChunk27.literals, 8061 ≤ key c ∧ key c < 8223 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder27.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder27.bounds c hc
    omega
  have b28 : increasing PV_CBM_CellChunk28.literals ∧ ∀ c ∈ PV_CBM_CellChunk28.literals, 8223 ≤ key c ∧ key c < 8573 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder28.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder28.bounds c hc
    omega
  have b29 : increasing PV_CBM_CellChunk29.literals ∧ ∀ c ∈ PV_CBM_CellChunk29.literals, 8573 ≤ key c ∧ key c < 8910 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder29.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder29.bounds c hc
    omega
  have b30 : increasing PV_CBM_CellChunk30.literals ∧ ∀ c ∈ PV_CBM_CellChunk30.literals, 8910 ≤ key c ∧ key c < 9156 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder30.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder30.bounds c hc
    omega
  have b31 : increasing PV_CBM_CellChunk31.literals ∧ ∀ c ∈ PV_CBM_CellChunk31.literals, 9156 ≤ key c ∧ key c < 9422 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder31.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder31.bounds c hc
    omega
  have b32 : increasing PV_CBM_CellChunk32.literals ∧ ∀ c ∈ PV_CBM_CellChunk32.literals, 9422 ≤ key c ∧ key c < 9759 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder32.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder32.bounds c hc
    omega
  have b33 : increasing PV_CBM_CellChunk33.literals ∧ ∀ c ∈ PV_CBM_CellChunk33.literals, 9759 ≤ key c ∧ key c < 10109 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder33.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder33.bounds c hc
    omega
  have b34 : increasing PV_CBM_CellChunk34.literals ∧ ∀ c ∈ PV_CBM_CellChunk34.literals, 10109 ≤ key c ∧ key c < 10205 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder34.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder34.bounds c hc
    omega
  have b35 : increasing PV_CBM_CellChunk35.literals ∧ ∀ c ∈ PV_CBM_CellChunk35.literals, 10205 ≤ key c ∧ key c < 10493 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder35.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder35.bounds c hc
    omega
  have b36 : increasing PV_CBM_CellChunk36.literals ∧ ∀ c ∈ PV_CBM_CellChunk36.literals, 10493 ≤ key c ∧ key c < 10830 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder36.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder36.bounds c hc
    omega
  have b37 : increasing PV_CBM_CellChunk37.literals ∧ ∀ c ∈ PV_CBM_CellChunk37.literals, 10830 ≤ key c ∧ key c < 11155 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder37.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder37.bounds c hc
    omega
  have b38 : increasing PV_CBM_CellChunk38.literals ∧ ∀ c ∈ PV_CBM_CellChunk38.literals, 11155 ≤ key c ∧ key c < 11240 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder38.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder38.bounds c hc
    omega
  have b39 : increasing PV_CBM_CellChunk39.literals ∧ ∀ c ∈ PV_CBM_CellChunk39.literals, 11240 ≤ key c ∧ key c < 11550 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder39.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder39.bounds c hc
    omega
  have b40 : increasing PV_CBM_CellChunk40.literals ∧ ∀ c ∈ PV_CBM_CellChunk40.literals, 11550 ≤ key c ∧ key c < 11887 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder40.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder40.bounds c hc
    omega
  have b41 : increasing PV_CBM_CellChunk41.literals ∧ ∀ c ∈ PV_CBM_CellChunk41.literals, 11887 ≤ key c ∧ key c < 12188 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder41.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder41.bounds c hc
    omega
  have b42 : increasing PV_CBM_CellChunk42.literals ∧ ∀ c ∈ PV_CBM_CellChunk42.literals, 12188 ≤ key c ∧ key c < 12273 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder42.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder42.bounds c hc
    omega
  have b43 : increasing PV_CBM_CellChunk43.literals ∧ ∀ c ∈ PV_CBM_CellChunk43.literals, 12273 ≤ key c ∧ key c < 12558 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder43.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder43.bounds c hc
    omega
  have b44 : increasing PV_CBM_CellChunk44.literals ∧ ∀ c ∈ PV_CBM_CellChunk44.literals, 12558 ≤ key c ∧ key c < 12895 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder44.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder44.bounds c hc
    omega
  have b45 : increasing PV_CBM_CellChunk45.literals ∧ ∀ c ∈ PV_CBM_CellChunk45.literals, 12895 ≤ key c ∧ key c < 13208 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder45.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder45.bounds c hc
    omega
  have b46 : increasing PV_CBM_CellChunk46.literals ∧ ∀ c ∈ PV_CBM_CellChunk46.literals, 13208 ≤ key c ∧ key c < 13293 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder46.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder46.bounds c hc
    omega
  have b47 : increasing PV_CBM_CellChunk47.literals ∧ ∀ c ∈ PV_CBM_CellChunk47.literals, 13293 ≤ key c ∧ key c < 13566 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder47.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder47.bounds c hc
    omega
  have b48 : increasing PV_CBM_CellChunk48.literals ∧ ∀ c ∈ PV_CBM_CellChunk48.literals, 13566 ≤ key c ∧ key c < 13903 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder48.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder48.bounds c hc
    omega
  have b49 : increasing PV_CBM_CellChunk49.literals ∧ ∀ c ∈ PV_CBM_CellChunk49.literals, 13903 ≤ key c ∧ key c < 14228 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder49.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder49.bounds c hc
    omega
  have b50 : increasing PV_CBM_CellChunk50.literals ∧ ∀ c ∈ PV_CBM_CellChunk50.literals, 14228 ≤ key c ∧ key c < 14313 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder50.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder50.bounds c hc
    omega
  have b51 : increasing PV_CBM_CellChunk51.literals ∧ ∀ c ∈ PV_CBM_CellChunk51.literals, 14313 ≤ key c ∧ key c < 14574 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder51.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder51.bounds c hc
    omega
  have b52 : increasing PV_CBM_CellChunk52.literals ∧ ∀ c ∈ PV_CBM_CellChunk52.literals, 14574 ≤ key c ∧ key c < 14911 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder52.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder52.bounds c hc
    omega
  have b53 : increasing PV_CBM_CellChunk53.literals ∧ ∀ c ∈ PV_CBM_CellChunk53.literals, 14911 ≤ key c ∧ key c < 15248 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder53.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder53.bounds c hc
    omega
  have b54 : increasing PV_CBM_CellChunk54.literals ∧ ∀ c ∈ PV_CBM_CellChunk54.literals, 15248 ≤ key c ∧ key c < 15333 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder54.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder54.bounds c hc
    omega
  have b55 : increasing PV_CBM_CellChunk55.literals ∧ ∀ c ∈ PV_CBM_CellChunk55.literals, 15333 ≤ key c ∧ key c < 15582 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder55.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder55.bounds c hc
    omega
  have b56 : increasing PV_CBM_CellChunk56.literals ∧ ∀ c ∈ PV_CBM_CellChunk56.literals, 15582 ≤ key c ∧ key c < 15919 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder56.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder56.bounds c hc
    omega
  have b57 : increasing PV_CBM_CellChunk57.literals ∧ ∀ c ∈ PV_CBM_CellChunk57.literals, 15919 ≤ key c ∧ key c < 16269 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder57.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder57.bounds c hc
    omega
  have b58 : increasing PV_CBM_CellChunk58.literals ∧ ∀ c ∈ PV_CBM_CellChunk58.literals, 16269 ≤ key c ∧ key c < 16353 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder58.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder58.bounds c hc
    omega
  have b59 : increasing PV_CBM_CellChunk59.literals ∧ ∀ c ∈ PV_CBM_CellChunk59.literals, 16353 ≤ key c ∧ key c < 16384 ∧ c.row.val < 1024 ∧ c.column.val < 16 := by
    refine ⟨PV_Op134_CellOrder59.sorted, ?_⟩
    intro c hc
    have := PV_Op134_CellOrder59.bounds c hc
    omega
  have h58 := append_bounds b58 (by decide) (by decide) b59
  have h57 := append_bounds b57 (by decide) (by decide) h58
  have h56 := append_bounds b56 (by decide) (by decide) h57
  have h55 := append_bounds b55 (by decide) (by decide) h56
  have h54 := append_bounds b54 (by decide) (by decide) h55
  have h53 := append_bounds b53 (by decide) (by decide) h54
  have h52 := append_bounds b52 (by decide) (by decide) h53
  have h51 := append_bounds b51 (by decide) (by decide) h52
  have h50 := append_bounds b50 (by decide) (by decide) h51
  have h49 := append_bounds b49 (by decide) (by decide) h50
  have h48 := append_bounds b48 (by decide) (by decide) h49
  have h47 := append_bounds b47 (by decide) (by decide) h48
  have h46 := append_bounds b46 (by decide) (by decide) h47
  have h45 := append_bounds b45 (by decide) (by decide) h46
  have h44 := append_bounds b44 (by decide) (by decide) h45
  have h43 := append_bounds b43 (by decide) (by decide) h44
  have h42 := append_bounds b42 (by decide) (by decide) h43
  have h41 := append_bounds b41 (by decide) (by decide) h42
  have h40 := append_bounds b40 (by decide) (by decide) h41
  have h39 := append_bounds b39 (by decide) (by decide) h40
  have h38 := append_bounds b38 (by decide) (by decide) h39
  have h37 := append_bounds b37 (by decide) (by decide) h38
  have h36 := append_bounds b36 (by decide) (by decide) h37
  have h35 := append_bounds b35 (by decide) (by decide) h36
  have h34 := append_bounds b34 (by decide) (by decide) h35
  have h33 := append_bounds b33 (by decide) (by decide) h34
  have h32 := append_bounds b32 (by decide) (by decide) h33
  have h31 := append_bounds b31 (by decide) (by decide) h32
  have h30 := append_bounds b30 (by decide) (by decide) h31
  have h29 := append_bounds b29 (by decide) (by decide) h30
  have h28 := append_bounds b28 (by decide) (by decide) h29
  have h27 := append_bounds b27 (by decide) (by decide) h28
  have h26 := append_bounds b26 (by decide) (by decide) h27
  have h25 := append_bounds b25 (by decide) (by decide) h26
  have h24 := append_bounds b24 (by decide) (by decide) h25
  have h23 := append_bounds b23 (by decide) (by decide) h24
  have h22 := append_bounds b22 (by decide) (by decide) h23
  have h21 := append_bounds b21 (by decide) (by decide) h22
  have h20 := append_bounds b20 (by decide) (by decide) h21
  have h19 := append_bounds b19 (by decide) (by decide) h20
  have h18 := append_bounds b18 (by decide) (by decide) h19
  have h17 := append_bounds b17 (by decide) (by decide) h18
  have h16 := append_bounds b16 (by decide) (by decide) h17
  have h15 := append_bounds b15 (by decide) (by decide) h16
  have h14 := append_bounds b14 (by decide) (by decide) h15
  have h13 := append_bounds b13 (by decide) (by decide) h14
  have h12 := append_bounds b12 (by decide) (by decide) h13
  have h11 := append_bounds b11 (by decide) (by decide) h12
  have h10 := append_bounds b10 (by decide) (by decide) h11
  have h9 := append_bounds b9 (by decide) (by decide) h10
  have h8 := append_bounds b8 (by decide) (by decide) h9
  have h7 := append_bounds b7 (by decide) (by decide) h8
  have h6 := append_bounds b6 (by decide) (by decide) h7
  have h5 := append_bounds b5 (by decide) (by decide) h6
  have h4 := append_bounds b4 (by decide) (by decide) h5
  have h3 := append_bounds b3 (by decide) (by decide) h4
  have h2 := append_bounds b2 (by decide) (by decide) h3
  have h1 := append_bounds b1 (by decide) (by decide) h2
  have h0 := append_bounds b0 (by decide) (by decide) h1
  exact h0

theorem nodup : PV_CBM_CellsSpec.literals.Nodup := PV_Op134_Order.nodup ordered_bounds.1
theorem complete (row column : Nat) (hr : row < 1024) (hc : column < 16)
    (hf : PV_CBM_InventoryShape.free row column) :
    ∃ c ∈ PV_CBM_CellsSpec.literals, c.row.val = row ∧ c.column.val = column := by
  exact PV_Op134_Coverage.complete _ nodup
    (by intro c hc; have h := ordered_bounds.2 c hc; exact ⟨h.2.2.1,h.2.2.2⟩)
    PV_CBM_CellsSpec.all_free PV_CBM_CellsSpec.length row column hr hc hf
#print axioms ordered_bounds
#print axioms nodup
#print axioms complete
end R1Z.PV_Op134_Inventory
