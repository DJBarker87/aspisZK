import AspisV8R19.R816BlockSixSourceView
import AspisV8R19.R813FiniteFunctionExt39
import AspisV8R19.R812P0StaticChunk00
import AspisV8R19.R812P0StaticChunk01
import AspisV8R19.R812P0StaticChunk02
import AspisV8R19.R812P0StaticChunk03
import AspisV8R19.R812P0StaticChunk04
set_option autoImplicit false
namespace AspisV8R19.R812BlockSixP0SourceRow
open AspisV8R19.R816BlockSixSourceView AspisV8R19.R807SourceBlock01Binding AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R813FiniteFunctionExt39
open AspisV8R19.R812SourceBlock06P0StaticChunk00 AspisV8R19.R812SourceBlock06P0StaticChunk01 AspisV8R19.R812SourceBlock06P0StaticChunk02 AspisV8R19.R812SourceBlock06P0StaticChunk03 AspisV8R19.R812SourceBlock06P0StaticChunk04
noncomputable section
abbrev M := R807SourceBlock01Binding.M
def p0Values : Fin 39 → M := ![0,0,0,0,0,4320,21888,0,0,0,0,0,0,0,0,0,0,0,0,0,1610612724,1610612724,1758,13602,1073739662,1073723870,2147481010,2147463244,3366,27054,2147480131,2147313751,4323,227988,5274,254844,1610606082,0,0]
theorem source_p0_values : (fun j : Fin 39 => fixedSourceMatrix (pointPosition 0) (block06Columns j)) = p0Values := by
  apply fin39_ext
  · simpa [p0Values, block06Columns] using static_p0_d028_s1_flat35
  · simpa [p0Values, block06Columns] using static_p0_d029_s0_flat36
  · simpa [p0Values, block06Columns] using static_p0_d029_s1_flat37
  · simpa [p0Values, block06Columns] using static_p0_d030_s0_flat38
  · simpa [p0Values, block06Columns] using static_p0_d030_s1_flat39
  · simpa [p0Values, block06Columns] using static_p0_d031_s0_flat40
  · simpa [p0Values, block06Columns] using static_p0_d031_s1_flat41
  · simpa [p0Values, block06Columns] using static_p0_d048_s1_flat42
  · simpa [p0Values, block06Columns] using static_p0_d049_s0_flat43
  · simpa [p0Values, block06Columns] using static_p0_d049_s1_flat44
  · simpa [p0Values, block06Columns] using static_p0_d050_s0_flat45
  · simpa [p0Values, block06Columns] using static_p0_d050_s1_flat46
  · simpa [p0Values, block06Columns] using static_p0_d051_s0_flat47
  · simpa [p0Values, block06Columns] using static_p0_d051_s1_flat48
  · simpa [p0Values, block06Columns] using static_p0_d052_s0_flat49
  · simpa [p0Values, block06Columns] using static_p0_d052_s1_flat50
  · simpa [p0Values, block06Columns] using static_p0_d053_s0_flat51
  · simpa [p0Values, block06Columns] using static_p0_d053_s1_flat52
  · simpa [p0Values, block06Columns] using static_p0_d054_s0_flat53
  · simpa [p0Values, block06Columns] using static_p0_d054_s1_flat54
  · simpa [p0Values, block06Columns] using static_p0_d055_s0_flat55
  · simpa [p0Values, block06Columns] using static_p0_d055_s1_flat56
  · simpa [p0Values, block06Columns] using static_p0_d056_s0_flat57
  · simpa [p0Values, block06Columns] using static_p0_d056_s1_flat58
  · simpa [p0Values, block06Columns] using static_p0_d057_s0_flat59
  · simpa [p0Values, block06Columns] using static_p0_d057_s1_flat60
  · simpa [p0Values, block06Columns] using static_p0_d058_s0_flat61
  · simpa [p0Values, block06Columns] using static_p0_d058_s1_flat62
  · simpa [p0Values, block06Columns] using static_p0_d059_s0_flat63
  · simpa [p0Values, block06Columns] using static_p0_d059_s1_flat64
  · simpa [p0Values, block06Columns] using static_p0_d060_s0_flat65
  · simpa [p0Values, block06Columns] using static_p0_d060_s2_flat66
  · simpa [p0Values, block06Columns] using static_p0_d061_s0_flat67
  · simpa [p0Values, block06Columns] using static_p0_d061_s2_flat68
  · simpa [p0Values, block06Columns] using static_p0_d062_s0_flat69
  · simpa [p0Values, block06Columns] using static_p0_d062_s2_flat70
  · simpa [p0Values, block06Columns] using static_p0_d063_s0_flat71
  · simpa [p0Values, block06Columns] using static_p0_d027_s2_flat72
  · simpa [p0Values, block06Columns] using static_p0_d047_s2_flat73
#print axioms source_p0_values
end
end AspisV8R19.R812BlockSixP0SourceRow
