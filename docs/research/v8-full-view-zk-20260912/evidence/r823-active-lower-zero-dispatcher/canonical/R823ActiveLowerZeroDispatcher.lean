import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R823Fin222AbstractDispatcher
import AspisV8R19.R811SourceLowerZeroChunk01
import AspisV8R19.R811SourceLowerZeroChunk02
import AspisV8R19.R811SourceLowerZeroChunk03
import AspisV8R19.R811SourceLowerZeroChunk04
import AspisV8R19.R811SourceLowerZeroChunk05
import AspisV8R19.R811SourceLowerZeroChunk06
import AspisV8R19.R811SourceLowerZeroChunk07
import AspisV8R19.R811SourceLowerZeroChunk08
import AspisV8R19.R811SourceLowerZeroChunk09
import AspisV8R19.R811SourceLowerZeroChunk10
import AspisV8R19.R811SourceLowerZeroChunk11
import AspisV8R19.R811SourceLowerZeroChunk12
import AspisV8R19.R811SourceLowerZeroChunk13
import AspisV8R19.R811SourceLowerZeroChunk14
import AspisV8R19.R811SourceLowerZeroChunk15
import AspisV8R19.R811SourceLowerZeroChunk16
import AspisV8R19.R811SourceLowerZeroChunk17
import AspisV8R19.R811SourceLowerZeroChunk18
import AspisV8R19.R811SourceLowerZeroChunk19
import AspisV8R19.R811SourceLowerZeroChunk20
import AspisV8R19.R811SourceLowerZeroChunk21
import AspisV8R19.R811SourceLowerZeroChunk22
import AspisV8R19.R811SourceLowerZeroChunk23
import AspisV8R19.R811SourceLowerZeroChunk24
import AspisV8R19.R811SourceLowerZeroChunk25
import AspisV8R19.R811SourceLowerZeroChunk26
import AspisV8R19.R811SourceLowerZeroChunk27
import AspisV8R19.R811SourceLowerZeroChunk28
import AspisV8R19.R811SourceLowerZeroChunk29
import AspisV8R19.R811SourceLowerZeroChunk30
import AspisV8R19.R811SourceLowerZeroChunk31
import AspisV8R19.R811SourceLowerZeroChunk32
import AspisV8R19.R811SourceLowerZeroChunk33
import AspisV8R19.R811SourceLowerZeroChunk34
import AspisV8R19.R811SourceLowerZeroChunk35
import AspisV8R19.R811SourceLowerZeroChunk36
import AspisV8R19.R811SourceLowerZeroChunk37
import AspisV8R19.R811SourceLowerZeroChunk38
import AspisV8R19.R811SourceLowerZeroChunk39
import AspisV8R19.R811SourceLowerZeroChunk40
import AspisV8R19.R811SourceLowerZeroChunk41
import AspisV8R19.R811SourceLowerZeroChunk42
import AspisV8R19.R811SourceLowerZeroChunk43
import AspisV8R19.R811SourceLowerZeroChunk44
import AspisV8R19.R811SourceLowerZeroChunk45
import AspisV8R19.R811SourceLowerZeroChunk46
import AspisV8R19.R811SourceLowerZeroChunk47
import AspisV8R19.R811SourceLowerZeroChunk48
import AspisV8R19.R811SourceLowerZeroChunk49
import AspisV8R19.R811SourceLowerZeroChunk50
import AspisV8R19.R811SourceLowerZeroChunk51
import AspisV8R19.R811SourceLowerZeroChunk52
import AspisV8R19.R811SourceLowerZeroChunk53
import AspisV8R19.R811SourceLowerZeroChunk54
import AspisV8R19.R811SourceLowerZeroPrototype

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R823ActiveLowerZeroDispatcher
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R766BlockOrderEquivalences
noncomputable section

theorem active_flat_eligible (i : Fin 214) :
    6 ≤ (rowOrderInv (activePosition i)).val ∧
    (rowOrderInv (activePosition i)).val ≠ 72 ∧
    (rowOrderInv (activePosition i)).val ≠ 73 := by
  revert i
  decide

theorem active_row_lower_zero (i : Fin 214) (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition i))) :
    fixedSourceMatrix (activePosition i) (colOrder j) = 0 := by
  let P : Fin 222 → Prop := fun r => ∀ k : Fin 222, blockLabel k < blockLabel r → reorderedSourceMatrix r k = 0
  have hP : P (rowOrderInv (activePosition i)) := by
    apply AspisV8R19.R823Fin222AbstractDispatcher.dispatch_active_flats (P := P)
      (h6 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk09.rowFlat6_lower_zero k hk)
      (h7 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk08.rowFlat7_lower_zero k hk)
      (h8 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk08.rowFlat8_lower_zero k hk)
      (h9 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk09.rowFlat9_lower_zero k hk)
      (h10 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk06.rowFlat10_lower_zero k hk)
      (h11 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk06.rowFlat11_lower_zero k hk)
      (h12 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk07.rowFlat12_lower_zero k hk)
      (h13 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk07.rowFlat13_lower_zero k hk)
      (h14 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk07.rowFlat14_lower_zero k hk)
      (h15 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk07.rowFlat15_lower_zero k hk)
      (h16 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk08.rowFlat16_lower_zero k hk)
      (h17 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk08.rowFlat17_lower_zero k hk)
      (h18 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk02.rowFlat18_lower_zero k hk)
      (h19 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk02.rowFlat19_lower_zero k hk)
      (h20 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk03.rowFlat20_lower_zero k hk)
      (h21 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk03.rowFlat21_lower_zero k hk)
      (h22 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk03.rowFlat22_lower_zero k hk)
      (h23 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk03.rowFlat23_lower_zero k hk)
      (h24 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk04.rowFlat24_lower_zero k hk)
      (h25 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk04.rowFlat25_lower_zero k hk)
      (h26 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk04.rowFlat26_lower_zero k hk)
      (h27 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk04.rowFlat27_lower_zero k hk)
      (h28 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk05.rowFlat28_lower_zero k hk)
      (h29 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk05.rowFlat29_lower_zero k hk)
      (h30 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk05.rowFlat30_lower_zero k hk)
      (h31 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk05.rowFlat31_lower_zero k hk)
      (h32 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk06.rowFlat32_lower_zero k hk)
      (h33 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk06.rowFlat33_lower_zero k hk)
      (h34 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk09.rowFlat34_lower_zero k hk)
      (h35 := fun k hk => AspisV8R19.R811SourceLowerZeroPrototype.rowFlat35_lower_zero k hk)
      (h36 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk01.rowFlat36_lower_zero k hk)
      (h37 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk01.rowFlat37_lower_zero k hk)
      (h38 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk01.rowFlat38_lower_zero k hk)
      (h39 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk01.rowFlat39_lower_zero k hk)
      (h40 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk02.rowFlat40_lower_zero k hk)
      (h41 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk02.rowFlat41_lower_zero k hk)
      (h42 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk09.rowFlat42_lower_zero k hk)
      (h43 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk10.rowFlat43_lower_zero k hk)
      (h44 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk10.rowFlat44_lower_zero k hk)
      (h45 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk10.rowFlat45_lower_zero k hk)
      (h46 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk10.rowFlat46_lower_zero k hk)
      (h47 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk11.rowFlat47_lower_zero k hk)
      (h48 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk11.rowFlat48_lower_zero k hk)
      (h49 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk11.rowFlat49_lower_zero k hk)
      (h50 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk11.rowFlat50_lower_zero k hk)
      (h51 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk12.rowFlat51_lower_zero k hk)
      (h52 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk12.rowFlat52_lower_zero k hk)
      (h53 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk12.rowFlat53_lower_zero k hk)
      (h54 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk12.rowFlat54_lower_zero k hk)
      (h55 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk13.rowFlat55_lower_zero k hk)
      (h56 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk13.rowFlat56_lower_zero k hk)
      (h57 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk13.rowFlat57_lower_zero k hk)
      (h58 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk13.rowFlat58_lower_zero k hk)
      (h59 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk14.rowFlat59_lower_zero k hk)
      (h60 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk14.rowFlat60_lower_zero k hk)
      (h61 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk14.rowFlat61_lower_zero k hk)
      (h62 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk14.rowFlat62_lower_zero k hk)
      (h63 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk15.rowFlat63_lower_zero k hk)
      (h64 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk15.rowFlat64_lower_zero k hk)
      (h65 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk15.rowFlat65_lower_zero k hk)
      (h66 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk15.rowFlat66_lower_zero k hk)
      (h67 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk16.rowFlat67_lower_zero k hk)
      (h68 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk16.rowFlat68_lower_zero k hk)
      (h69 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk16.rowFlat69_lower_zero k hk)
      (h70 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk16.rowFlat70_lower_zero k hk)
      (h71 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk17.rowFlat71_lower_zero k hk)
      (h74 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk23.rowFlat74_lower_zero k hk)
      (h75 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk23.rowFlat75_lower_zero k hk)
      (h76 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk21.rowFlat76_lower_zero k hk)
      (h77 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk21.rowFlat77_lower_zero k hk)
      (h78 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk21.rowFlat78_lower_zero k hk)
      (h79 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk22.rowFlat79_lower_zero k hk)
      (h80 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk22.rowFlat80_lower_zero k hk)
      (h81 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk22.rowFlat81_lower_zero k hk)
      (h82 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk22.rowFlat82_lower_zero k hk)
      (h83 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk23.rowFlat83_lower_zero k hk)
      (h84 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk17.rowFlat84_lower_zero k hk)
      (h85 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk17.rowFlat85_lower_zero k hk)
      (h86 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk17.rowFlat86_lower_zero k hk)
      (h87 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk18.rowFlat87_lower_zero k hk)
      (h88 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk18.rowFlat88_lower_zero k hk)
      (h89 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk18.rowFlat89_lower_zero k hk)
      (h90 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk18.rowFlat90_lower_zero k hk)
      (h91 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk19.rowFlat91_lower_zero k hk)
      (h92 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk19.rowFlat92_lower_zero k hk)
      (h93 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk19.rowFlat93_lower_zero k hk)
      (h94 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk19.rowFlat94_lower_zero k hk)
      (h95 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk20.rowFlat95_lower_zero k hk)
      (h96 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk20.rowFlat96_lower_zero k hk)
      (h97 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk20.rowFlat97_lower_zero k hk)
      (h98 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk20.rowFlat98_lower_zero k hk)
      (h99 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk21.rowFlat99_lower_zero k hk)
      (h100 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk30.rowFlat100_lower_zero k hk)
      (h101 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk29.rowFlat101_lower_zero k hk)
      (h102 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk29.rowFlat102_lower_zero k hk)
      (h103 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk29.rowFlat103_lower_zero k hk)
      (h104 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk29.rowFlat104_lower_zero k hk)
      (h105 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk25.rowFlat105_lower_zero k hk)
      (h106 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk25.rowFlat106_lower_zero k hk)
      (h107 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk25.rowFlat107_lower_zero k hk)
      (h108 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk25.rowFlat108_lower_zero k hk)
      (h109 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk26.rowFlat109_lower_zero k hk)
      (h110 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk26.rowFlat110_lower_zero k hk)
      (h111 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk26.rowFlat111_lower_zero k hk)
      (h112 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk26.rowFlat112_lower_zero k hk)
      (h113 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk27.rowFlat113_lower_zero k hk)
      (h114 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk27.rowFlat114_lower_zero k hk)
      (h115 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk27.rowFlat115_lower_zero k hk)
      (h116 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk27.rowFlat116_lower_zero k hk)
      (h117 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk28.rowFlat117_lower_zero k hk)
      (h118 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk28.rowFlat118_lower_zero k hk)
      (h119 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk28.rowFlat119_lower_zero k hk)
      (h120 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk28.rowFlat120_lower_zero k hk)
      (h121 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk24.rowFlat121_lower_zero k hk)
      (h122 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk24.rowFlat122_lower_zero k hk)
      (h123 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk24.rowFlat123_lower_zero k hk)
      (h124 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk24.rowFlat124_lower_zero k hk)
      (h125 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk23.rowFlat125_lower_zero k hk)
      (h126 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk31.rowFlat126_lower_zero k hk)
      (h127 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk31.rowFlat127_lower_zero k hk)
      (h128 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk32.rowFlat128_lower_zero k hk)
      (h129 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk32.rowFlat129_lower_zero k hk)
      (h130 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk31.rowFlat130_lower_zero k hk)
      (h131 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk31.rowFlat131_lower_zero k hk)
      (h132 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk30.rowFlat132_lower_zero k hk)
      (h133 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk30.rowFlat133_lower_zero k hk)
      (h134 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk30.rowFlat134_lower_zero k hk)
      (h135 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk33.rowFlat135_lower_zero k hk)
      (h136 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk33.rowFlat136_lower_zero k hk)
      (h137 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk33.rowFlat137_lower_zero k hk)
      (h138 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk34.rowFlat138_lower_zero k hk)
      (h139 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk32.rowFlat139_lower_zero k hk)
      (h140 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk33.rowFlat140_lower_zero k hk)
      (h141 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk32.rowFlat141_lower_zero k hk)
      (h142 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk34.rowFlat142_lower_zero k hk)
      (h143 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk34.rowFlat143_lower_zero k hk)
      (h144 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk34.rowFlat144_lower_zero k hk)
      (h145 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk35.rowFlat145_lower_zero k hk)
      (h146 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk35.rowFlat146_lower_zero k hk)
      (h147 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk35.rowFlat147_lower_zero k hk)
      (h148 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk35.rowFlat148_lower_zero k hk)
      (h149 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk36.rowFlat149_lower_zero k hk)
      (h150 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk37.rowFlat150_lower_zero k hk)
      (h151 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk37.rowFlat151_lower_zero k hk)
      (h152 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk37.rowFlat152_lower_zero k hk)
      (h153 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk37.rowFlat153_lower_zero k hk)
      (h154 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk36.rowFlat154_lower_zero k hk)
      (h155 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk36.rowFlat155_lower_zero k hk)
      (h156 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk36.rowFlat156_lower_zero k hk)
      (h157 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk38.rowFlat157_lower_zero k hk)
      (h158 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk39.rowFlat158_lower_zero k hk)
      (h159 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk39.rowFlat159_lower_zero k hk)
      (h160 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk39.rowFlat160_lower_zero k hk)
      (h161 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk38.rowFlat161_lower_zero k hk)
      (h162 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk38.rowFlat162_lower_zero k hk)
      (h163 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk38.rowFlat163_lower_zero k hk)
      (h164 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk45.rowFlat164_lower_zero k hk)
      (h165 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk46.rowFlat165_lower_zero k hk)
      (h166 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk45.rowFlat166_lower_zero k hk)
      (h167 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk45.rowFlat167_lower_zero k hk)
      (h168 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk43.rowFlat168_lower_zero k hk)
      (h169 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk43.rowFlat169_lower_zero k hk)
      (h170 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk43.rowFlat170_lower_zero k hk)
      (h171 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk44.rowFlat171_lower_zero k hk)
      (h172 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk44.rowFlat172_lower_zero k hk)
      (h173 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk44.rowFlat173_lower_zero k hk)
      (h174 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk44.rowFlat174_lower_zero k hk)
      (h175 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk45.rowFlat175_lower_zero k hk)
      (h176 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk41.rowFlat176_lower_zero k hk)
      (h177 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk41.rowFlat177_lower_zero k hk)
      (h178 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk41.rowFlat178_lower_zero k hk)
      (h179 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk42.rowFlat179_lower_zero k hk)
      (h180 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk42.rowFlat180_lower_zero k hk)
      (h181 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk42.rowFlat181_lower_zero k hk)
      (h182 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk42.rowFlat182_lower_zero k hk)
      (h183 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk43.rowFlat183_lower_zero k hk)
      (h184 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk40.rowFlat184_lower_zero k hk)
      (h185 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk40.rowFlat185_lower_zero k hk)
      (h186 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk40.rowFlat186_lower_zero k hk)
      (h187 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk41.rowFlat187_lower_zero k hk)
      (h188 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk39.rowFlat188_lower_zero k hk)
      (h189 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk40.rowFlat189_lower_zero k hk)
      (h190 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk53.rowFlat190_lower_zero k hk)
      (h191 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk53.rowFlat191_lower_zero k hk)
      (h192 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk54.rowFlat192_lower_zero k hk)
      (h193 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk52.rowFlat193_lower_zero k hk)
      (h194 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk52.rowFlat194_lower_zero k hk)
      (h195 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk53.rowFlat195_lower_zero k hk)
      (h196 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk53.rowFlat196_lower_zero k hk)
      (h197 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk50.rowFlat197_lower_zero k hk)
      (h198 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk50.rowFlat198_lower_zero k hk)
      (h199 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk51.rowFlat199_lower_zero k hk)
      (h200 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk51.rowFlat200_lower_zero k hk)
      (h201 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk51.rowFlat201_lower_zero k hk)
      (h202 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk51.rowFlat202_lower_zero k hk)
      (h203 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk52.rowFlat203_lower_zero k hk)
      (h204 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk52.rowFlat204_lower_zero k hk)
      (h205 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk46.rowFlat205_lower_zero k hk)
      (h206 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk46.rowFlat206_lower_zero k hk)
      (h207 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk47.rowFlat207_lower_zero k hk)
      (h208 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk47.rowFlat208_lower_zero k hk)
      (h209 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk47.rowFlat209_lower_zero k hk)
      (h210 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk47.rowFlat210_lower_zero k hk)
      (h211 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk48.rowFlat211_lower_zero k hk)
      (h212 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk48.rowFlat212_lower_zero k hk)
      (h213 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk48.rowFlat213_lower_zero k hk)
      (h214 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk48.rowFlat214_lower_zero k hk)
      (h215 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk49.rowFlat215_lower_zero k hk)
      (h216 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk49.rowFlat216_lower_zero k hk)
      (h217 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk49.rowFlat217_lower_zero k hk)
      (h218 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk49.rowFlat218_lower_zero k hk)
      (h219 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk50.rowFlat219_lower_zero k hk)
      (h220 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk50.rowFlat220_lower_zero k hk)
      (h221 := fun k hk => AspisV8R19.R811SourceLowerZeroChunk46.rowFlat221_lower_zero k hk)
      (rowOrderInv (activePosition i))
      (active_flat_eligible i).1
      (active_flat_eligible i).2.1
      (active_flat_eligible i).2.2
  have hentry := hP j h
  change fixedSourceMatrix (rowOrder (rowOrderInv (activePosition i))) (colOrder j) = 0 at hentry
  rw [row_right] at hentry
  exact hentry

#print axioms active_flat_eligible
#print axioms active_row_lower_zero
end
end AspisV8R19.R823ActiveLowerZeroDispatcher
