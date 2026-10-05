import AspisV8R19.R816BlockSixSourceView
import AspisV8R19.R813FiniteFunctionExt39
import AspisV8R19.R812P2StaticChunk00
import AspisV8R19.R812P2StaticChunk01
import AspisV8R19.R812P2StaticChunk02
import AspisV8R19.R812P2StaticChunk03
import AspisV8R19.R812P2StaticChunk04
set_option autoImplicit false
namespace AspisV8R19.R812BlockSixP2SourceRow
open AspisV8R19.R816BlockSixSourceView AspisV8R19.R807SourceBlock01Binding AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R813FiniteFunctionExt39
open AspisV8R19.R812SourceBlock06P2StaticChunk00 AspisV8R19.R812SourceBlock06P2StaticChunk01 AspisV8R19.R812SourceBlock06P2StaticChunk02 AspisV8R19.R812SourceBlock06P2StaticChunk03 AspisV8R19.R812SourceBlock06P2StaticChunk04
noncomputable section
abbrev M := R807SourceBlock01Binding.M
def p2Values : Fin 39 → M := ![0,0,0,0,0,12960,65664,0,0,0,0,0,0,0,0,0,0,0,0,0,536870908,536870908,586,4534,1073741103,1073735839,2147482768,2147476846,1122,9018,2147482475,2147427015,1441,75996,1758,84948,536868694,0,0]
theorem source_p2_values : (fun j : Fin 39 => fixedSourceMatrix (pointPosition 2) (block06Columns j)) = p2Values := by
  apply fin39_ext
  · simpa [p2Values, block06Columns] using static_p2_d028_s1_flat35
  · simpa [p2Values, block06Columns] using static_p2_d029_s0_flat36
  · simpa [p2Values, block06Columns] using static_p2_d029_s1_flat37
  · simpa [p2Values, block06Columns] using static_p2_d030_s0_flat38
  · simpa [p2Values, block06Columns] using static_p2_d030_s1_flat39
  · simpa [p2Values, block06Columns] using static_p2_d031_s0_flat40
  · simpa [p2Values, block06Columns] using static_p2_d031_s1_flat41
  · simpa [p2Values, block06Columns] using static_p2_d048_s1_flat42
  · simpa [p2Values, block06Columns] using static_p2_d049_s0_flat43
  · simpa [p2Values, block06Columns] using static_p2_d049_s1_flat44
  · simpa [p2Values, block06Columns] using static_p2_d050_s0_flat45
  · simpa [p2Values, block06Columns] using static_p2_d050_s1_flat46
  · simpa [p2Values, block06Columns] using static_p2_d051_s0_flat47
  · simpa [p2Values, block06Columns] using static_p2_d051_s1_flat48
  · simpa [p2Values, block06Columns] using static_p2_d052_s0_flat49
  · simpa [p2Values, block06Columns] using static_p2_d052_s1_flat50
  · simpa [p2Values, block06Columns] using static_p2_d053_s0_flat51
  · simpa [p2Values, block06Columns] using static_p2_d053_s1_flat52
  · simpa [p2Values, block06Columns] using static_p2_d054_s0_flat53
  · simpa [p2Values, block06Columns] using static_p2_d054_s1_flat54
  · simpa [p2Values, block06Columns] using static_p2_d055_s0_flat55
  · simpa [p2Values, block06Columns] using static_p2_d055_s1_flat56
  · simpa [p2Values, block06Columns] using static_p2_d056_s0_flat57
  · simpa [p2Values, block06Columns] using static_p2_d056_s1_flat58
  · simpa [p2Values, block06Columns] using static_p2_d057_s0_flat59
  · simpa [p2Values, block06Columns] using static_p2_d057_s1_flat60
  · simpa [p2Values, block06Columns] using static_p2_d058_s0_flat61
  · simpa [p2Values, block06Columns] using static_p2_d058_s1_flat62
  · simpa [p2Values, block06Columns] using static_p2_d059_s0_flat63
  · simpa [p2Values, block06Columns] using static_p2_d059_s1_flat64
  · simpa [p2Values, block06Columns] using static_p2_d060_s0_flat65
  · simpa [p2Values, block06Columns] using static_p2_d060_s2_flat66
  · simpa [p2Values, block06Columns] using static_p2_d061_s0_flat67
  · simpa [p2Values, block06Columns] using static_p2_d061_s2_flat68
  · simpa [p2Values, block06Columns] using static_p2_d062_s0_flat69
  · simpa [p2Values, block06Columns] using static_p2_d062_s2_flat70
  · simpa [p2Values, block06Columns] using static_p2_d063_s0_flat71
  · simpa [p2Values, block06Columns] using static_p2_d027_s2_flat72
  · simpa [p2Values, block06Columns] using static_p2_d047_s2_flat73
#print axioms source_p2_values
end
end AspisV8R19.R812BlockSixP2SourceRow
