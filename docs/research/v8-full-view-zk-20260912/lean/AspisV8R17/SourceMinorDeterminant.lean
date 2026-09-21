import AspisV8R17.SourceWindowBlocks00
import AspisV8R17.SourceWindowBlocks01
import AspisV8R17.SourceWindowBlocks02
import AspisV8R17.SourceWindowBlocks03
import AspisV8R17.SourceWindowBlocks04
import AspisV8R17.SourceWindowBlocks05
import AspisV8R17.SourceWindowBlocks06
import AspisV8R17.SourceWindowBlocks07
import AspisV8R17.SourceWindowBlocks08
import AspisV8R17.SourceWindowBlocks09
import AspisV8R17.SourceWindowBlocks10
import AspisV8R17.SourceWindowBlocks11
import AspisV8R17.SourceWindowBlocks12
import AspisV8R17.SourceWindowBlocks13
import AspisV8R17.SourceWindowBlocks14
import AspisV8R17.SourceWindowBlocks15
import AspisV8R17.SourceWindowBlocks16

/-! Generated symbolic source-minor determinant composition.
Frozen block SHA256: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
Fixed algebraic witness only; not a source sampler or global privacy theorem. -/
set_option autoImplicit false
namespace AspisV8R17.SourceMinor.Windows

theorem tail133_unit : IsUnit (matrixWindow sourceMatrix 214 0).det := by
  rw [Matrix.det_isEmpty]
  exact isUnit_one
#print axioms tail133_unit

theorem tail132_unit : IsUnit (matrixWindow sourceMatrix 213 1).det := by
  exact matrixWindow_isUnit sourceMatrix 213 1 0
    block132_lower block132_unit tail133_unit
#print axioms tail132_unit

theorem tail131_unit : IsUnit (matrixWindow sourceMatrix 212 2).det := by
  exact matrixWindow_isUnit sourceMatrix 212 1 1
    block131_lower block131_unit tail132_unit
#print axioms tail131_unit

theorem tail130_unit : IsUnit (matrixWindow sourceMatrix 211 3).det := by
  exact matrixWindow_isUnit sourceMatrix 211 1 2
    block130_lower block130_unit tail131_unit
#print axioms tail130_unit

theorem tail129_unit : IsUnit (matrixWindow sourceMatrix 210 4).det := by
  exact matrixWindow_isUnit sourceMatrix 210 1 3
    block129_lower block129_unit tail130_unit
#print axioms tail129_unit

theorem tail128_unit : IsUnit (matrixWindow sourceMatrix 209 5).det := by
  exact matrixWindow_isUnit sourceMatrix 209 1 4
    block128_lower block128_unit tail129_unit
#print axioms tail128_unit

theorem tail127_unit : IsUnit (matrixWindow sourceMatrix 208 6).det := by
  exact matrixWindow_isUnit sourceMatrix 208 1 5
    block127_lower block127_unit tail128_unit
#print axioms tail127_unit

theorem tail126_unit : IsUnit (matrixWindow sourceMatrix 207 7).det := by
  exact matrixWindow_isUnit sourceMatrix 207 1 6
    block126_lower block126_unit tail127_unit
#print axioms tail126_unit

theorem tail125_unit : IsUnit (matrixWindow sourceMatrix 206 8).det := by
  exact matrixWindow_isUnit sourceMatrix 206 1 7
    block125_lower block125_unit tail126_unit
#print axioms tail125_unit

theorem tail124_unit : IsUnit (matrixWindow sourceMatrix 205 9).det := by
  exact matrixWindow_isUnit sourceMatrix 205 1 8
    block124_lower block124_unit tail125_unit
#print axioms tail124_unit

theorem tail123_unit : IsUnit (matrixWindow sourceMatrix 204 10).det := by
  exact matrixWindow_isUnit sourceMatrix 204 1 9
    block123_lower block123_unit tail124_unit
#print axioms tail123_unit

theorem tail122_unit : IsUnit (matrixWindow sourceMatrix 203 11).det := by
  exact matrixWindow_isUnit sourceMatrix 203 1 10
    block122_lower block122_unit tail123_unit
#print axioms tail122_unit

theorem tail121_unit : IsUnit (matrixWindow sourceMatrix 202 12).det := by
  exact matrixWindow_isUnit sourceMatrix 202 1 11
    block121_lower block121_unit tail122_unit
#print axioms tail121_unit

theorem tail120_unit : IsUnit (matrixWindow sourceMatrix 201 13).det := by
  exact matrixWindow_isUnit sourceMatrix 201 1 12
    block120_lower block120_unit tail121_unit
#print axioms tail120_unit

theorem tail119_unit : IsUnit (matrixWindow sourceMatrix 200 14).det := by
  exact matrixWindow_isUnit sourceMatrix 200 1 13
    block119_lower block119_unit tail120_unit
#print axioms tail119_unit

theorem tail118_unit : IsUnit (matrixWindow sourceMatrix 198 16).det := by
  exact matrixWindow_isUnit sourceMatrix 198 2 14
    block118_lower block118_unit tail119_unit
#print axioms tail118_unit

theorem tail117_unit : IsUnit (matrixWindow sourceMatrix 196 18).det := by
  exact matrixWindow_isUnit sourceMatrix 196 2 16
    block117_lower block117_unit tail118_unit
#print axioms tail117_unit

theorem tail116_unit : IsUnit (matrixWindow sourceMatrix 195 19).det := by
  exact matrixWindow_isUnit sourceMatrix 195 1 18
    block116_lower block116_unit tail117_unit
#print axioms tail116_unit

theorem tail115_unit : IsUnit (matrixWindow sourceMatrix 193 21).det := by
  exact matrixWindow_isUnit sourceMatrix 193 2 19
    block115_lower block115_unit tail116_unit
#print axioms tail115_unit

theorem tail114_unit : IsUnit (matrixWindow sourceMatrix 191 23).det := by
  exact matrixWindow_isUnit sourceMatrix 191 2 21
    block114_lower block114_unit tail115_unit
#print axioms tail114_unit

theorem tail113_unit : IsUnit (matrixWindow sourceMatrix 189 25).det := by
  exact matrixWindow_isUnit sourceMatrix 189 2 23
    block113_lower block113_unit tail114_unit
#print axioms tail113_unit

theorem tail112_unit : IsUnit (matrixWindow sourceMatrix 187 27).det := by
  exact matrixWindow_isUnit sourceMatrix 187 2 25
    block112_lower block112_unit tail113_unit
#print axioms tail112_unit

theorem tail111_unit : IsUnit (matrixWindow sourceMatrix 185 29).det := by
  exact matrixWindow_isUnit sourceMatrix 185 2 27
    block111_lower block111_unit tail112_unit
#print axioms tail111_unit

theorem tail110_unit : IsUnit (matrixWindow sourceMatrix 183 31).det := by
  exact matrixWindow_isUnit sourceMatrix 183 2 29
    block110_lower block110_unit tail111_unit
#print axioms tail110_unit

theorem tail109_unit : IsUnit (matrixWindow sourceMatrix 181 33).det := by
  exact matrixWindow_isUnit sourceMatrix 181 2 31
    block109_lower block109_unit tail110_unit
#print axioms tail109_unit

theorem tail108_unit : IsUnit (matrixWindow sourceMatrix 179 35).det := by
  exact matrixWindow_isUnit sourceMatrix 179 2 33
    block108_lower block108_unit tail109_unit
#print axioms tail108_unit

theorem tail107_unit : IsUnit (matrixWindow sourceMatrix 177 37).det := by
  exact matrixWindow_isUnit sourceMatrix 177 2 35
    block107_lower block107_unit tail108_unit
#print axioms tail107_unit

theorem tail106_unit : IsUnit (matrixWindow sourceMatrix 176 38).det := by
  exact matrixWindow_isUnit sourceMatrix 176 1 37
    block106_lower block106_unit tail107_unit
#print axioms tail106_unit

theorem tail105_unit : IsUnit (matrixWindow sourceMatrix 175 39).det := by
  exact matrixWindow_isUnit sourceMatrix 175 1 38
    block105_lower block105_unit tail106_unit
#print axioms tail105_unit

theorem tail104_unit : IsUnit (matrixWindow sourceMatrix 172 42).det := by
  exact matrixWindow_isUnit sourceMatrix 172 3 39
    block104_lower block104_unit tail105_unit
#print axioms tail104_unit

theorem tail103_unit : IsUnit (matrixWindow sourceMatrix 170 44).det := by
  exact matrixWindow_isUnit sourceMatrix 170 2 42
    block103_lower block103_unit tail104_unit
#print axioms tail103_unit

theorem tail102_unit : IsUnit (matrixWindow sourceMatrix 167 47).det := by
  exact matrixWindow_isUnit sourceMatrix 167 3 44
    block102_lower block102_unit tail103_unit
#print axioms tail102_unit

theorem tail101_unit : IsUnit (matrixWindow sourceMatrix 166 48).det := by
  exact matrixWindow_isUnit sourceMatrix 166 1 47
    block101_lower block101_unit tail102_unit
#print axioms tail101_unit

theorem tail100_unit : IsUnit (matrixWindow sourceMatrix 164 50).det := by
  exact matrixWindow_isUnit sourceMatrix 164 2 48
    block100_lower block100_unit tail101_unit
#print axioms tail100_unit

theorem tail99_unit : IsUnit (matrixWindow sourceMatrix 163 51).det := by
  exact matrixWindow_isUnit sourceMatrix 163 1 50
    block99_lower block99_unit tail100_unit
#print axioms tail99_unit

theorem tail98_unit : IsUnit (matrixWindow sourceMatrix 162 52).det := by
  exact matrixWindow_isUnit sourceMatrix 162 1 51
    block98_lower block98_unit tail99_unit
#print axioms tail98_unit

theorem tail97_unit : IsUnit (matrixWindow sourceMatrix 160 54).det := by
  exact matrixWindow_isUnit sourceMatrix 160 2 52
    block97_lower block97_unit tail98_unit
#print axioms tail97_unit

theorem tail96_unit : IsUnit (matrixWindow sourceMatrix 159 55).det := by
  exact matrixWindow_isUnit sourceMatrix 159 1 54
    block96_lower block96_unit tail97_unit
#print axioms tail96_unit

theorem tail95_unit : IsUnit (matrixWindow sourceMatrix 156 58).det := by
  exact matrixWindow_isUnit sourceMatrix 156 3 55
    block95_lower block95_unit tail96_unit
#print axioms tail95_unit

theorem tail94_unit : IsUnit (matrixWindow sourceMatrix 154 60).det := by
  exact matrixWindow_isUnit sourceMatrix 154 2 58
    block94_lower block94_unit tail95_unit
#print axioms tail94_unit

theorem tail93_unit : IsUnit (matrixWindow sourceMatrix 153 61).det := by
  exact matrixWindow_isUnit sourceMatrix 153 1 60
    block93_lower block93_unit tail94_unit
#print axioms tail93_unit

theorem tail92_unit : IsUnit (matrixWindow sourceMatrix 150 64).det := by
  exact matrixWindow_isUnit sourceMatrix 150 3 61
    block92_lower block92_unit tail93_unit
#print axioms tail92_unit

theorem tail91_unit : IsUnit (matrixWindow sourceMatrix 149 65).det := by
  exact matrixWindow_isUnit sourceMatrix 149 1 64
    block91_lower block91_unit tail92_unit
#print axioms tail91_unit

theorem tail90_unit : IsUnit (matrixWindow sourceMatrix 146 68).det := by
  exact matrixWindow_isUnit sourceMatrix 146 3 65
    block90_lower block90_unit tail91_unit
#print axioms tail90_unit

theorem tail89_unit : IsUnit (matrixWindow sourceMatrix 145 69).det := by
  exact matrixWindow_isUnit sourceMatrix 145 1 68
    block89_lower block89_unit tail90_unit
#print axioms tail89_unit

theorem tail88_unit : IsUnit (matrixWindow sourceMatrix 143 71).det := by
  exact matrixWindow_isUnit sourceMatrix 143 2 69
    block88_lower block88_unit tail89_unit
#print axioms tail88_unit

theorem tail87_unit : IsUnit (matrixWindow sourceMatrix 140 74).det := by
  exact matrixWindow_isUnit sourceMatrix 140 3 71
    block87_lower block87_unit tail88_unit
#print axioms tail87_unit

theorem tail86_unit : IsUnit (matrixWindow sourceMatrix 139 75).det := by
  exact matrixWindow_isUnit sourceMatrix 139 1 74
    block86_lower block86_unit tail87_unit
#print axioms tail86_unit

theorem tail85_unit : IsUnit (matrixWindow sourceMatrix 138 76).det := by
  exact matrixWindow_isUnit sourceMatrix 138 1 75
    block85_lower block85_unit tail86_unit
#print axioms tail85_unit

theorem tail84_unit : IsUnit (matrixWindow sourceMatrix 137 77).det := by
  exact matrixWindow_isUnit sourceMatrix 137 1 76
    block84_lower block84_unit tail85_unit
#print axioms tail84_unit

theorem tail83_unit : IsUnit (matrixWindow sourceMatrix 136 78).det := by
  exact matrixWindow_isUnit sourceMatrix 136 1 77
    block83_lower block83_unit tail84_unit
#print axioms tail83_unit

theorem tail82_unit : IsUnit (matrixWindow sourceMatrix 133 81).det := by
  exact matrixWindow_isUnit sourceMatrix 133 3 78
    block82_lower block82_unit tail83_unit
#print axioms tail82_unit

theorem tail81_unit : IsUnit (matrixWindow sourceMatrix 130 84).det := by
  exact matrixWindow_isUnit sourceMatrix 130 3 81
    block81_lower block81_unit tail82_unit
#print axioms tail81_unit

theorem tail80_unit : IsUnit (matrixWindow sourceMatrix 128 86).det := by
  exact matrixWindow_isUnit sourceMatrix 128 2 84
    block80_lower block80_unit tail81_unit
#print axioms tail80_unit

theorem tail79_unit : IsUnit (matrixWindow sourceMatrix 127 87).det := by
  exact matrixWindow_isUnit sourceMatrix 127 1 86
    block79_lower block79_unit tail80_unit
#print axioms tail79_unit

theorem tail78_unit : IsUnit (matrixWindow sourceMatrix 125 89).det := by
  exact matrixWindow_isUnit sourceMatrix 125 2 87
    block78_lower block78_unit tail79_unit
#print axioms tail78_unit

theorem tail77_unit : IsUnit (matrixWindow sourceMatrix 123 91).det := by
  exact matrixWindow_isUnit sourceMatrix 123 2 89
    block77_lower block77_unit tail78_unit
#print axioms tail77_unit

theorem tail76_unit : IsUnit (matrixWindow sourceMatrix 122 92).det := by
  exact matrixWindow_isUnit sourceMatrix 122 1 91
    block76_lower block76_unit tail77_unit
#print axioms tail76_unit

theorem tail75_unit : IsUnit (matrixWindow sourceMatrix 120 94).det := by
  exact matrixWindow_isUnit sourceMatrix 120 2 92
    block75_lower block75_unit tail76_unit
#print axioms tail75_unit

theorem tail74_unit : IsUnit (matrixWindow sourceMatrix 118 96).det := by
  exact matrixWindow_isUnit sourceMatrix 118 2 94
    block74_lower block74_unit tail75_unit
#print axioms tail74_unit

theorem tail73_unit : IsUnit (matrixWindow sourceMatrix 116 98).det := by
  exact matrixWindow_isUnit sourceMatrix 116 2 96
    block73_lower block73_unit tail74_unit
#print axioms tail73_unit

theorem tail72_unit : IsUnit (matrixWindow sourceMatrix 114 100).det := by
  exact matrixWindow_isUnit sourceMatrix 114 2 98
    block72_lower block72_unit tail73_unit
#print axioms tail72_unit

theorem tail71_unit : IsUnit (matrixWindow sourceMatrix 112 102).det := by
  exact matrixWindow_isUnit sourceMatrix 112 2 100
    block71_lower block71_unit tail72_unit
#print axioms tail71_unit

theorem tail70_unit : IsUnit (matrixWindow sourceMatrix 110 104).det := by
  exact matrixWindow_isUnit sourceMatrix 110 2 102
    block70_lower block70_unit tail71_unit
#print axioms tail70_unit

theorem tail69_unit : IsUnit (matrixWindow sourceMatrix 108 106).det := by
  exact matrixWindow_isUnit sourceMatrix 108 2 104
    block69_lower block69_unit tail70_unit
#print axioms tail69_unit

theorem tail68_unit : IsUnit (matrixWindow sourceMatrix 106 108).det := by
  exact matrixWindow_isUnit sourceMatrix 106 2 106
    block68_lower block68_unit tail69_unit
#print axioms tail68_unit

theorem tail67_unit : IsUnit (matrixWindow sourceMatrix 104 110).det := by
  exact matrixWindow_isUnit sourceMatrix 104 2 108
    block67_lower block67_unit tail68_unit
#print axioms tail67_unit

theorem tail66_unit : IsUnit (matrixWindow sourceMatrix 102 112).det := by
  exact matrixWindow_isUnit sourceMatrix 102 2 110
    block66_lower block66_unit tail67_unit
#print axioms tail66_unit

theorem tail65_unit : IsUnit (matrixWindow sourceMatrix 100 114).det := by
  exact matrixWindow_isUnit sourceMatrix 100 2 112
    block65_lower block65_unit tail66_unit
#print axioms tail65_unit

theorem tail64_unit : IsUnit (matrixWindow sourceMatrix 98 116).det := by
  exact matrixWindow_isUnit sourceMatrix 98 2 114
    block64_lower block64_unit tail65_unit
#print axioms tail64_unit

theorem tail63_unit : IsUnit (matrixWindow sourceMatrix 96 118).det := by
  exact matrixWindow_isUnit sourceMatrix 96 2 116
    block63_lower block63_unit tail64_unit
#print axioms tail63_unit

theorem tail62_unit : IsUnit (matrixWindow sourceMatrix 94 120).det := by
  exact matrixWindow_isUnit sourceMatrix 94 2 118
    block62_lower block62_unit tail63_unit
#print axioms tail62_unit

theorem tail61_unit : IsUnit (matrixWindow sourceMatrix 92 122).det := by
  exact matrixWindow_isUnit sourceMatrix 92 2 120
    block61_lower block61_unit tail62_unit
#print axioms tail61_unit

theorem tail60_unit : IsUnit (matrixWindow sourceMatrix 90 124).det := by
  exact matrixWindow_isUnit sourceMatrix 90 2 122
    block60_lower block60_unit tail61_unit
#print axioms tail60_unit

theorem tail59_unit : IsUnit (matrixWindow sourceMatrix 88 126).det := by
  exact matrixWindow_isUnit sourceMatrix 88 2 124
    block59_lower block59_unit tail60_unit
#print axioms tail59_unit

theorem tail58_unit : IsUnit (matrixWindow sourceMatrix 86 128).det := by
  exact matrixWindow_isUnit sourceMatrix 86 2 126
    block58_lower block58_unit tail59_unit
#print axioms tail58_unit

theorem tail57_unit : IsUnit (matrixWindow sourceMatrix 85 129).det := by
  exact matrixWindow_isUnit sourceMatrix 85 1 128
    block57_lower block57_unit tail58_unit
#print axioms tail57_unit

theorem tail56_unit : IsUnit (matrixWindow sourceMatrix 83 131).det := by
  exact matrixWindow_isUnit sourceMatrix 83 2 129
    block56_lower block56_unit tail57_unit
#print axioms tail56_unit

theorem tail55_unit : IsUnit (matrixWindow sourceMatrix 82 132).det := by
  exact matrixWindow_isUnit sourceMatrix 82 1 131
    block55_lower block55_unit tail56_unit
#print axioms tail55_unit

theorem tail54_unit : IsUnit (matrixWindow sourceMatrix 80 134).det := by
  exact matrixWindow_isUnit sourceMatrix 80 2 132
    block54_lower block54_unit tail55_unit
#print axioms tail54_unit

theorem tail53_unit : IsUnit (matrixWindow sourceMatrix 79 135).det := by
  exact matrixWindow_isUnit sourceMatrix 79 1 134
    block53_lower block53_unit tail54_unit
#print axioms tail53_unit

theorem tail52_unit : IsUnit (matrixWindow sourceMatrix 77 137).det := by
  exact matrixWindow_isUnit sourceMatrix 77 2 135
    block52_lower block52_unit tail53_unit
#print axioms tail52_unit

theorem tail51_unit : IsUnit (matrixWindow sourceMatrix 75 139).det := by
  exact matrixWindow_isUnit sourceMatrix 75 2 137
    block51_lower block51_unit tail52_unit
#print axioms tail51_unit

theorem tail50_unit : IsUnit (matrixWindow sourceMatrix 74 140).det := by
  exact matrixWindow_isUnit sourceMatrix 74 1 139
    block50_lower block50_unit tail51_unit
#print axioms tail50_unit

theorem tail49_unit : IsUnit (matrixWindow sourceMatrix 73 141).det := by
  exact matrixWindow_isUnit sourceMatrix 73 1 140
    block49_lower block49_unit tail50_unit
#print axioms tail49_unit

theorem tail48_unit : IsUnit (matrixWindow sourceMatrix 72 142).det := by
  exact matrixWindow_isUnit sourceMatrix 72 1 141
    block48_lower block48_unit tail49_unit
#print axioms tail48_unit

theorem tail47_unit : IsUnit (matrixWindow sourceMatrix 70 144).det := by
  exact matrixWindow_isUnit sourceMatrix 70 2 142
    block47_lower block47_unit tail48_unit
#print axioms tail47_unit

theorem tail46_unit : IsUnit (matrixWindow sourceMatrix 68 146).det := by
  exact matrixWindow_isUnit sourceMatrix 68 2 144
    block46_lower block46_unit tail47_unit
#print axioms tail46_unit

theorem tail45_unit : IsUnit (matrixWindow sourceMatrix 67 147).det := by
  exact matrixWindow_isUnit sourceMatrix 67 1 146
    block45_lower block45_unit tail46_unit
#print axioms tail45_unit

theorem tail44_unit : IsUnit (matrixWindow sourceMatrix 66 148).det := by
  exact matrixWindow_isUnit sourceMatrix 66 1 147
    block44_lower block44_unit tail45_unit
#print axioms tail44_unit

theorem tail43_unit : IsUnit (matrixWindow sourceMatrix 64 150).det := by
  exact matrixWindow_isUnit sourceMatrix 64 2 148
    block43_lower block43_unit tail44_unit
#print axioms tail43_unit

theorem tail42_unit : IsUnit (matrixWindow sourceMatrix 63 151).det := by
  exact matrixWindow_isUnit sourceMatrix 63 1 150
    block42_lower block42_unit tail43_unit
#print axioms tail42_unit

theorem tail41_unit : IsUnit (matrixWindow sourceMatrix 61 153).det := by
  exact matrixWindow_isUnit sourceMatrix 61 2 151
    block41_lower block41_unit tail42_unit
#print axioms tail41_unit

theorem tail40_unit : IsUnit (matrixWindow sourceMatrix 60 154).det := by
  exact matrixWindow_isUnit sourceMatrix 60 1 153
    block40_lower block40_unit tail41_unit
#print axioms tail40_unit

theorem tail39_unit : IsUnit (matrixWindow sourceMatrix 58 156).det := by
  exact matrixWindow_isUnit sourceMatrix 58 2 154
    block39_lower block39_unit tail40_unit
#print axioms tail39_unit

theorem tail38_unit : IsUnit (matrixWindow sourceMatrix 57 157).det := by
  exact matrixWindow_isUnit sourceMatrix 57 1 156
    block38_lower block38_unit tail39_unit
#print axioms tail38_unit

theorem tail37_unit : IsUnit (matrixWindow sourceMatrix 55 159).det := by
  exact matrixWindow_isUnit sourceMatrix 55 2 157
    block37_lower block37_unit tail38_unit
#print axioms tail37_unit

theorem tail36_unit : IsUnit (matrixWindow sourceMatrix 54 160).det := by
  exact matrixWindow_isUnit sourceMatrix 54 1 159
    block36_lower block36_unit tail37_unit
#print axioms tail36_unit

theorem tail35_unit : IsUnit (matrixWindow sourceMatrix 52 162).det := by
  exact matrixWindow_isUnit sourceMatrix 52 2 160
    block35_lower block35_unit tail36_unit
#print axioms tail35_unit

theorem tail34_unit : IsUnit (matrixWindow sourceMatrix 51 163).det := by
  exact matrixWindow_isUnit sourceMatrix 51 1 162
    block34_lower block34_unit tail35_unit
#print axioms tail34_unit

theorem tail33_unit : IsUnit (matrixWindow sourceMatrix 49 165).det := by
  exact matrixWindow_isUnit sourceMatrix 49 2 163
    block33_lower block33_unit tail34_unit
#print axioms tail33_unit

theorem tail32_unit : IsUnit (matrixWindow sourceMatrix 48 166).det := by
  exact matrixWindow_isUnit sourceMatrix 48 1 165
    block32_lower block32_unit tail33_unit
#print axioms tail32_unit

theorem tail31_unit : IsUnit (matrixWindow sourceMatrix 46 168).det := by
  exact matrixWindow_isUnit sourceMatrix 46 2 166
    block31_lower block31_unit tail32_unit
#print axioms tail31_unit

theorem tail30_unit : IsUnit (matrixWindow sourceMatrix 45 169).det := by
  exact matrixWindow_isUnit sourceMatrix 45 1 168
    block30_lower block30_unit tail31_unit
#print axioms tail30_unit

theorem tail29_unit : IsUnit (matrixWindow sourceMatrix 43 171).det := by
  exact matrixWindow_isUnit sourceMatrix 43 2 169
    block29_lower block29_unit tail30_unit
#print axioms tail29_unit

theorem tail28_unit : IsUnit (matrixWindow sourceMatrix 42 172).det := by
  exact matrixWindow_isUnit sourceMatrix 42 1 171
    block28_lower block28_unit tail29_unit
#print axioms tail28_unit

theorem tail27_unit : IsUnit (matrixWindow sourceMatrix 40 174).det := by
  exact matrixWindow_isUnit sourceMatrix 40 2 172
    block27_lower block27_unit tail28_unit
#print axioms tail27_unit

theorem tail26_unit : IsUnit (matrixWindow sourceMatrix 39 175).det := by
  exact matrixWindow_isUnit sourceMatrix 39 1 174
    block26_lower block26_unit tail27_unit
#print axioms tail26_unit

theorem tail25_unit : IsUnit (matrixWindow sourceMatrix 37 177).det := by
  exact matrixWindow_isUnit sourceMatrix 37 2 175
    block25_lower block25_unit tail26_unit
#print axioms tail25_unit

theorem tail24_unit : IsUnit (matrixWindow sourceMatrix 36 178).det := by
  exact matrixWindow_isUnit sourceMatrix 36 1 177
    block24_lower block24_unit tail25_unit
#print axioms tail24_unit

theorem tail23_unit : IsUnit (matrixWindow sourceMatrix 34 180).det := by
  exact matrixWindow_isUnit sourceMatrix 34 2 178
    block23_lower block23_unit tail24_unit
#print axioms tail23_unit

theorem tail22_unit : IsUnit (matrixWindow sourceMatrix 33 181).det := by
  exact matrixWindow_isUnit sourceMatrix 33 1 180
    block22_lower block22_unit tail23_unit
#print axioms tail22_unit

theorem tail21_unit : IsUnit (matrixWindow sourceMatrix 31 183).det := by
  exact matrixWindow_isUnit sourceMatrix 31 2 181
    block21_lower block21_unit tail22_unit
#print axioms tail21_unit

theorem tail20_unit : IsUnit (matrixWindow sourceMatrix 30 184).det := by
  exact matrixWindow_isUnit sourceMatrix 30 1 183
    block20_lower block20_unit tail21_unit
#print axioms tail20_unit

theorem tail19_unit : IsUnit (matrixWindow sourceMatrix 28 186).det := by
  exact matrixWindow_isUnit sourceMatrix 28 2 184
    block19_lower block19_unit tail20_unit
#print axioms tail19_unit

theorem tail18_unit : IsUnit (matrixWindow sourceMatrix 27 187).det := by
  exact matrixWindow_isUnit sourceMatrix 27 1 186
    block18_lower block18_unit tail19_unit
#print axioms tail18_unit

theorem tail17_unit : IsUnit (matrixWindow sourceMatrix 25 189).det := by
  exact matrixWindow_isUnit sourceMatrix 25 2 187
    block17_lower block17_unit tail18_unit
#print axioms tail17_unit

theorem tail16_unit : IsUnit (matrixWindow sourceMatrix 24 190).det := by
  exact matrixWindow_isUnit sourceMatrix 24 1 189
    block16_lower block16_unit tail17_unit
#print axioms tail16_unit

theorem tail15_unit : IsUnit (matrixWindow sourceMatrix 22 192).det := by
  exact matrixWindow_isUnit sourceMatrix 22 2 190
    block15_lower block15_unit tail16_unit
#print axioms tail15_unit

theorem tail14_unit : IsUnit (matrixWindow sourceMatrix 21 193).det := by
  exact matrixWindow_isUnit sourceMatrix 21 1 192
    block14_lower block14_unit tail15_unit
#print axioms tail14_unit

theorem tail13_unit : IsUnit (matrixWindow sourceMatrix 19 195).det := by
  exact matrixWindow_isUnit sourceMatrix 19 2 193
    block13_lower block13_unit tail14_unit
#print axioms tail13_unit

theorem tail12_unit : IsUnit (matrixWindow sourceMatrix 18 196).det := by
  exact matrixWindow_isUnit sourceMatrix 18 1 195
    block12_lower block12_unit tail13_unit
#print axioms tail12_unit

theorem tail11_unit : IsUnit (matrixWindow sourceMatrix 16 198).det := by
  exact matrixWindow_isUnit sourceMatrix 16 2 196
    block11_lower block11_unit tail12_unit
#print axioms tail11_unit

theorem tail10_unit : IsUnit (matrixWindow sourceMatrix 15 199).det := by
  exact matrixWindow_isUnit sourceMatrix 15 1 198
    block10_lower block10_unit tail11_unit
#print axioms tail10_unit

theorem tail9_unit : IsUnit (matrixWindow sourceMatrix 13 201).det := by
  exact matrixWindow_isUnit sourceMatrix 13 2 199
    block9_lower block9_unit tail10_unit
#print axioms tail9_unit

theorem tail8_unit : IsUnit (matrixWindow sourceMatrix 12 202).det := by
  exact matrixWindow_isUnit sourceMatrix 12 1 201
    block8_lower block8_unit tail9_unit
#print axioms tail8_unit

theorem tail7_unit : IsUnit (matrixWindow sourceMatrix 10 204).det := by
  exact matrixWindow_isUnit sourceMatrix 10 2 202
    block7_lower block7_unit tail8_unit
#print axioms tail7_unit

theorem tail6_unit : IsUnit (matrixWindow sourceMatrix 9 205).det := by
  exact matrixWindow_isUnit sourceMatrix 9 1 204
    block6_lower block6_unit tail7_unit
#print axioms tail6_unit

theorem tail5_unit : IsUnit (matrixWindow sourceMatrix 8 206).det := by
  exact matrixWindow_isUnit sourceMatrix 8 1 205
    block5_lower block5_unit tail6_unit
#print axioms tail5_unit

theorem tail4_unit : IsUnit (matrixWindow sourceMatrix 6 208).det := by
  exact matrixWindow_isUnit sourceMatrix 6 2 206
    block4_lower block4_unit tail5_unit
#print axioms tail4_unit

theorem tail3_unit : IsUnit (matrixWindow sourceMatrix 5 209).det := by
  exact matrixWindow_isUnit sourceMatrix 5 1 208
    block3_lower block3_unit tail4_unit
#print axioms tail3_unit

theorem tail2_unit : IsUnit (matrixWindow sourceMatrix 3 211).det := by
  exact matrixWindow_isUnit sourceMatrix 3 2 209
    block2_lower block2_unit tail3_unit
#print axioms tail2_unit

theorem tail1_unit : IsUnit (matrixWindow sourceMatrix 1 213).det := by
  exact matrixWindow_isUnit sourceMatrix 1 2 211
    block1_lower block1_unit tail2_unit
#print axioms tail1_unit

theorem tail0_unit : IsUnit (matrixWindow sourceMatrix 0 214).det := by
  exact matrixWindow_isUnit sourceMatrix 0 1 213
    block0_lower block0_unit tail1_unit
#print axioms tail0_unit

theorem ordered_minor_det_isUnit :
    IsUnit (Matrix.det (orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7))) := by
  have h := tail0_unit
  rw [full_window_eq] at h
  exact h

theorem source_minor_det_ne_zero :
    Matrix.det (minor (1073741824 : ZMod 2147483647) 2 13 11 (-7)) ≠ 0 := by
  letI : Fact (1 < (2147483647 : ℕ)) := ⟨by decide⟩
  have h := ordered_minor_det_isUnit.ne_zero
  change Matrix.det (Matrix.reindex BlockOrdering.rowPerm.symm BlockOrdering.columnPerm.symm
    (minor (1073741824 : ZMod 2147483647) 2 13 11 (-7))) ≠ 0 at h
  rw [Matrix.det_reindex] at h
  intro hz
  exact h (by rw [hz, mul_zero])

#print axioms ordered_minor_det_isUnit
#print axioms source_minor_det_ne_zero
end AspisV8R17.SourceMinor.Windows
