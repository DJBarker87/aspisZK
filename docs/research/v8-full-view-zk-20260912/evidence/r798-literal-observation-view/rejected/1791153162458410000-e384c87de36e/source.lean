import AspisV8R19.R797ObservationEncoding
import AspisV8R19.R790LiteralObservationChunk13
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R798LiteralObservationView
open AspisV8R19.R797ObservationEncoding
open AspisV8R19.R746SelectedJointMinor
noncomputable section

-- Literal list access and 222 small integer pairs only; no field recurrence is reduced.
def sourceObservations : List Obs := [
AspisV8R19.R790LiteralObservationOrderPrototype.obs0,
AspisV8R19.R790LiteralObservationOrderPrototype.obs1,
AspisV8R19.R790LiteralObservationOrderPrototype.obs2,
AspisV8R19.R790LiteralObservationOrderPrototype.obs3,
AspisV8R19.R790LiteralObservationOrderPrototype.obs4,
AspisV8R19.R790LiteralObservationOrderPrototype.obs5,
AspisV8R19.R790LiteralObservationOrderPrototype.obs6,
AspisV8R19.R790LiteralObservationOrderPrototype.obs7,
AspisV8R19.R790LiteralObservationChunk00.obs_008,
AspisV8R19.R790LiteralObservationChunk00.obs_009,
AspisV8R19.R790LiteralObservationChunk00.obs_010,
AspisV8R19.R790LiteralObservationChunk00.obs_011,
AspisV8R19.R790LiteralObservationChunk00.obs_012,
AspisV8R19.R790LiteralObservationChunk00.obs_013,
AspisV8R19.R790LiteralObservationChunk00.obs_014,
AspisV8R19.R790LiteralObservationChunk00.obs_015,
AspisV8R19.R790LiteralObservationChunk00.obs_016,
AspisV8R19.R790LiteralObservationChunk00.obs_017,
AspisV8R19.R790LiteralObservationChunk00.obs_018,
AspisV8R19.R790LiteralObservationChunk00.obs_019,
AspisV8R19.R790LiteralObservationChunk00.obs_020,
AspisV8R19.R790LiteralObservationChunk00.obs_021,
AspisV8R19.R790LiteralObservationChunk00.obs_022,
AspisV8R19.R790LiteralObservationChunk00.obs_023,
AspisV8R19.R790LiteralObservationChunk01.obs_024,
AspisV8R19.R790LiteralObservationChunk01.obs_025,
AspisV8R19.R790LiteralObservationChunk01.obs_026,
AspisV8R19.R790LiteralObservationChunk01.obs_027,
AspisV8R19.R790LiteralObservationChunk01.obs_028,
AspisV8R19.R790LiteralObservationChunk01.obs_029,
AspisV8R19.R790LiteralObservationChunk01.obs_030,
AspisV8R19.R790LiteralObservationChunk01.obs_031,
AspisV8R19.R790LiteralObservationChunk01.obs_032,
AspisV8R19.R790LiteralObservationChunk01.obs_033,
AspisV8R19.R790LiteralObservationChunk01.obs_034,
AspisV8R19.R790LiteralObservationChunk01.obs_035,
AspisV8R19.R790LiteralObservationChunk01.obs_036,
AspisV8R19.R790LiteralObservationChunk01.obs_037,
AspisV8R19.R790LiteralObservationChunk01.obs_038,
AspisV8R19.R790LiteralObservationChunk01.obs_039,
AspisV8R19.R790LiteralObservationChunk02.obs_040,
AspisV8R19.R790LiteralObservationChunk02.obs_041,
AspisV8R19.R790LiteralObservationChunk02.obs_042,
AspisV8R19.R790LiteralObservationChunk02.obs_043,
AspisV8R19.R790LiteralObservationChunk02.obs_044,
AspisV8R19.R790LiteralObservationChunk02.obs_045,
AspisV8R19.R790LiteralObservationChunk02.obs_046,
AspisV8R19.R790LiteralObservationChunk02.obs_047,
AspisV8R19.R790LiteralObservationChunk02.obs_048,
AspisV8R19.R790LiteralObservationChunk02.obs_049,
AspisV8R19.R790LiteralObservationChunk02.obs_050,
AspisV8R19.R790LiteralObservationChunk02.obs_051,
AspisV8R19.R790LiteralObservationChunk02.obs_052,
AspisV8R19.R790LiteralObservationChunk02.obs_053,
AspisV8R19.R790LiteralObservationChunk02.obs_054,
AspisV8R19.R790LiteralObservationChunk02.obs_055,
AspisV8R19.R790LiteralObservationChunk03.obs_056,
AspisV8R19.R790LiteralObservationChunk03.obs_057,
AspisV8R19.R790LiteralObservationChunk03.obs_058,
AspisV8R19.R790LiteralObservationChunk03.obs_059,
AspisV8R19.R790LiteralObservationChunk03.obs_060,
AspisV8R19.R790LiteralObservationChunk03.obs_061,
AspisV8R19.R790LiteralObservationChunk03.obs_062,
AspisV8R19.R790LiteralObservationChunk03.obs_063,
AspisV8R19.R790LiteralObservationChunk03.obs_064,
AspisV8R19.R790LiteralObservationChunk03.obs_065,
AspisV8R19.R790LiteralObservationChunk03.obs_066,
AspisV8R19.R790LiteralObservationChunk03.obs_067,
AspisV8R19.R790LiteralObservationChunk03.obs_068,
AspisV8R19.R790LiteralObservationChunk03.obs_069,
AspisV8R19.R790LiteralObservationChunk03.obs_070,
AspisV8R19.R790LiteralObservationChunk03.obs_071,
AspisV8R19.R790LiteralObservationChunk04.obs_072,
AspisV8R19.R790LiteralObservationChunk04.obs_073,
AspisV8R19.R790LiteralObservationChunk04.obs_074,
AspisV8R19.R790LiteralObservationChunk04.obs_075,
AspisV8R19.R790LiteralObservationChunk04.obs_076,
AspisV8R19.R790LiteralObservationChunk04.obs_077,
AspisV8R19.R790LiteralObservationChunk04.obs_078,
AspisV8R19.R790LiteralObservationChunk04.obs_079,
AspisV8R19.R790LiteralObservationChunk04.obs_080,
AspisV8R19.R790LiteralObservationChunk04.obs_081,
AspisV8R19.R790LiteralObservationChunk04.obs_082,
AspisV8R19.R790LiteralObservationChunk04.obs_083,
AspisV8R19.R790LiteralObservationChunk04.obs_084,
AspisV8R19.R790LiteralObservationChunk04.obs_085,
AspisV8R19.R790LiteralObservationChunk04.obs_086,
AspisV8R19.R790LiteralObservationChunk04.obs_087,
AspisV8R19.R790LiteralObservationChunk05.obs_088,
AspisV8R19.R790LiteralObservationChunk05.obs_089,
AspisV8R19.R790LiteralObservationChunk05.obs_090,
AspisV8R19.R790LiteralObservationChunk05.obs_091,
AspisV8R19.R790LiteralObservationChunk05.obs_092,
AspisV8R19.R790LiteralObservationChunk05.obs_093,
AspisV8R19.R790LiteralObservationChunk05.obs_094,
AspisV8R19.R790LiteralObservationChunk05.obs_095,
AspisV8R19.R790LiteralObservationChunk05.obs_096,
AspisV8R19.R790LiteralObservationChunk05.obs_097,
AspisV8R19.R790LiteralObservationChunk05.obs_098,
AspisV8R19.R790LiteralObservationChunk05.obs_099,
AspisV8R19.R790LiteralObservationChunk05.obs_100,
AspisV8R19.R790LiteralObservationChunk05.obs_101,
AspisV8R19.R790LiteralObservationChunk05.obs_102,
AspisV8R19.R790LiteralObservationChunk05.obs_103,
AspisV8R19.R790LiteralObservationChunk06.obs_104,
AspisV8R19.R790LiteralObservationChunk06.obs_105,
AspisV8R19.R790LiteralObservationChunk06.obs_106,
AspisV8R19.R790LiteralObservationChunk06.obs_107,
AspisV8R19.R790LiteralObservationChunk06.obs_108,
AspisV8R19.R790LiteralObservationChunk06.obs_109,
AspisV8R19.R790LiteralObservationChunk06.obs_110,
AspisV8R19.R790LiteralObservationChunk06.obs_111,
AspisV8R19.R790LiteralObservationChunk06.obs_112,
AspisV8R19.R790LiteralObservationChunk06.obs_113,
AspisV8R19.R790LiteralObservationChunk06.obs_114,
AspisV8R19.R790LiteralObservationChunk06.obs_115,
AspisV8R19.R790LiteralObservationChunk06.obs_116,
AspisV8R19.R790LiteralObservationChunk06.obs_117,
AspisV8R19.R790LiteralObservationChunk06.obs_118,
AspisV8R19.R790LiteralObservationChunk06.obs_119,
AspisV8R19.R790LiteralObservationChunk07.obs_120,
AspisV8R19.R790LiteralObservationChunk07.obs_121,
AspisV8R19.R790LiteralObservationChunk07.obs_122,
AspisV8R19.R790LiteralObservationChunk07.obs_123,
AspisV8R19.R790LiteralObservationChunk07.obs_124,
AspisV8R19.R790LiteralObservationChunk07.obs_125,
AspisV8R19.R790LiteralObservationChunk07.obs_126,
AspisV8R19.R790LiteralObservationChunk07.obs_127,
AspisV8R19.R790LiteralObservationChunk07.obs_128,
AspisV8R19.R790LiteralObservationChunk07.obs_129,
AspisV8R19.R790LiteralObservationChunk07.obs_130,
AspisV8R19.R790LiteralObservationChunk07.obs_131,
AspisV8R19.R790LiteralObservationChunk07.obs_132,
AspisV8R19.R790LiteralObservationChunk07.obs_133,
AspisV8R19.R790LiteralObservationChunk07.obs_134,
AspisV8R19.R790LiteralObservationChunk07.obs_135,
AspisV8R19.R790LiteralObservationChunk08.obs_136,
AspisV8R19.R790LiteralObservationChunk08.obs_137,
AspisV8R19.R790LiteralObservationChunk08.obs_138,
AspisV8R19.R790LiteralObservationChunk08.obs_139,
AspisV8R19.R790LiteralObservationChunk08.obs_140,
AspisV8R19.R790LiteralObservationChunk08.obs_141,
AspisV8R19.R790LiteralObservationChunk08.obs_142,
AspisV8R19.R790LiteralObservationChunk08.obs_143,
AspisV8R19.R790LiteralObservationChunk08.obs_144,
AspisV8R19.R790LiteralObservationChunk08.obs_145,
AspisV8R19.R790LiteralObservationChunk08.obs_146,
AspisV8R19.R790LiteralObservationChunk08.obs_147,
AspisV8R19.R790LiteralObservationChunk08.obs_148,
AspisV8R19.R790LiteralObservationChunk08.obs_149,
AspisV8R19.R790LiteralObservationChunk08.obs_150,
AspisV8R19.R790LiteralObservationChunk08.obs_151,
AspisV8R19.R790LiteralObservationChunk09.obs_152,
AspisV8R19.R790LiteralObservationChunk09.obs_153,
AspisV8R19.R790LiteralObservationChunk09.obs_154,
AspisV8R19.R790LiteralObservationChunk09.obs_155,
AspisV8R19.R790LiteralObservationChunk09.obs_156,
AspisV8R19.R790LiteralObservationChunk09.obs_157,
AspisV8R19.R790LiteralObservationChunk09.obs_158,
AspisV8R19.R790LiteralObservationChunk09.obs_159,
AspisV8R19.R790LiteralObservationChunk09.obs_160,
AspisV8R19.R790LiteralObservationChunk09.obs_161,
AspisV8R19.R790LiteralObservationChunk09.obs_162,
AspisV8R19.R790LiteralObservationChunk09.obs_163,
AspisV8R19.R790LiteralObservationChunk09.obs_164,
AspisV8R19.R790LiteralObservationChunk09.obs_165,
AspisV8R19.R790LiteralObservationChunk09.obs_166,
AspisV8R19.R790LiteralObservationChunk09.obs_167,
AspisV8R19.R790LiteralObservationChunk10.obs_168,
AspisV8R19.R790LiteralObservationChunk10.obs_169,
AspisV8R19.R790LiteralObservationChunk10.obs_170,
AspisV8R19.R790LiteralObservationChunk10.obs_171,
AspisV8R19.R790LiteralObservationChunk10.obs_172,
AspisV8R19.R790LiteralObservationChunk10.obs_173,
AspisV8R19.R790LiteralObservationChunk10.obs_174,
AspisV8R19.R790LiteralObservationChunk10.obs_175,
AspisV8R19.R790LiteralObservationChunk10.obs_176,
AspisV8R19.R790LiteralObservationChunk10.obs_177,
AspisV8R19.R790LiteralObservationChunk10.obs_178,
AspisV8R19.R790LiteralObservationChunk10.obs_179,
AspisV8R19.R790LiteralObservationChunk10.obs_180,
AspisV8R19.R790LiteralObservationChunk10.obs_181,
AspisV8R19.R790LiteralObservationChunk10.obs_182,
AspisV8R19.R790LiteralObservationChunk10.obs_183,
AspisV8R19.R790LiteralObservationChunk11.obs_184,
AspisV8R19.R790LiteralObservationChunk11.obs_185,
AspisV8R19.R790LiteralObservationChunk11.obs_186,
AspisV8R19.R790LiteralObservationChunk11.obs_187,
AspisV8R19.R790LiteralObservationChunk11.obs_188,
AspisV8R19.R790LiteralObservationChunk11.obs_189,
AspisV8R19.R790LiteralObservationChunk11.obs_190,
AspisV8R19.R790LiteralObservationChunk11.obs_191,
AspisV8R19.R790LiteralObservationChunk11.obs_192,
AspisV8R19.R790LiteralObservationChunk11.obs_193,
AspisV8R19.R790LiteralObservationChunk11.obs_194,
AspisV8R19.R790LiteralObservationChunk11.obs_195,
AspisV8R19.R790LiteralObservationChunk11.obs_196,
AspisV8R19.R790LiteralObservationChunk11.obs_197,
AspisV8R19.R790LiteralObservationChunk11.obs_198,
AspisV8R19.R790LiteralObservationChunk11.obs_199,
AspisV8R19.R790LiteralObservationChunk12.obs_200,
AspisV8R19.R790LiteralObservationChunk12.obs_201,
AspisV8R19.R790LiteralObservationChunk12.obs_202,
AspisV8R19.R790LiteralObservationChunk12.obs_203,
AspisV8R19.R790LiteralObservationChunk12.obs_204,
AspisV8R19.R790LiteralObservationChunk12.obs_205,
AspisV8R19.R790LiteralObservationChunk12.obs_206,
AspisV8R19.R790LiteralObservationChunk12.obs_207,
AspisV8R19.R790LiteralObservationChunk12.obs_208,
AspisV8R19.R790LiteralObservationChunk12.obs_209,
AspisV8R19.R790LiteralObservationChunk12.obs_210,
AspisV8R19.R790LiteralObservationChunk12.obs_211,
AspisV8R19.R790LiteralObservationChunk12.obs_212,
AspisV8R19.R790LiteralObservationChunk12.obs_top,
AspisV8R19.R790LiteralObservationChunk12.obs_point_0,
AspisV8R19.R790LiteralObservationChunk12.obs_point_1,
AspisV8R19.R790LiteralObservationChunk13.obs_point_2,
AspisV8R19.R790LiteralObservationChunk13.obs_coeff_0,
AspisV8R19.R790LiteralObservationChunk13.obs_coeff_1,
AspisV8R19.R790LiteralObservationChunk13.obs_coeff_2,
AspisV8R19.R790LiteralObservationChunk13.obs_coeff_3,
AspisV8R19.R790LiteralObservationChunk13.obs_coeff_4]
def literalKeys : List (Nat × Nat) := [(0,114), (0,116), (0,118), (0,120), (0,122), (0,124), (0,126), (0,128), (0,130), (0,132), (0,134), (0,136), (0,138), (0,140), (0,142), (0,144), (0,146), (0,148), (0,150), (0,152), (0,154), (0,156), (0,158), (0,160), (0,162), (0,164), (0,166), (0,168), (0,170), (0,172), (0,174), (0,176), (0,178), (0,180), (0,184), (0,190), (0,194), (0,196), (0,198), (0,200), (0,202), (0,204), (0,206), (0,208), (0,210), (0,212), (0,214), (0,216), (0,218), (0,220), (0,222), (0,224), (0,226), (0,228), (0,230), (0,232), (0,234), (0,236), (0,238), (0,240), (0,243), (0,245), (0,247), (0,249), (0,251), (0,253), (0,257), (0,259), (0,261), (0,263), (0,265), (0,267), (0,269), (0,271), (0,273), (0,275), (0,277), (0,279), (0,281), (0,283), (0,285), (0,287), (0,289), (0,291), (0,293), (0,295), (0,297), (0,299), (0,301), (0,303), (0,305), (0,307), (0,311), (0,313), (0,315), (0,317), (0,319), (0,321), (0,323), (0,325), (0,327), (0,329), (0,331), (0,333), (0,335), (0,337), (0,339), (0,341), (0,343), (0,345), (0,347), (0,349), (0,351), (0,353), (0,355), (0,357), (0,359), (0,361), (0,365), (0,367), (0,370), (0,372), (0,374), (0,376), (0,378), (0,380), (0,382), (0,499), (0,501), (0,503), (0,505), (0,507), (0,509), (0,511), (0,626), (0,628), (0,630), (0,632), (0,634), (0,636), (0,638), (0,639), (0,755), (0,757), (0,759), (0,761), (0,763), (0,765), (0,766), (0,882), (0,884), (0,886), (0,888), (0,890), (0,892), (0,894), (0,900), (0,902), (0,904), (0,906), (0,908), (0,910), (0,912), (0,914), (0,916), (0,918), (0,920), (0,922), (0,924), (0,926), (0,928), (0,930), (0,932), (0,934), (0,936), (0,938), (0,940), (0,942), (0,944), (0,948), (0,952), (0,954), (0,958), (0,960), (0,962), (0,964), (0,966), (0,968), (0,970), (0,972), (0,974), (0,976), (0,978), (0,980), (0,982), (0,984), (0,986), (0,988), (0,990), (0,992), (0,994), (0,996), (0,998), (0,1000), (0,1002), (0,1004), (0,1006), (0,1008), (0,1011), (0,1013), (0,1015), (0,1017), (0,1019), (0,1022), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2), (2,3), (2,4)]
theorem sourceObservations_length : sourceObservations.length = 222 := rfl
theorem sourceObservations_keys : sourceObservations.map observationKey = literalKeys := rfl
theorem literalKeys_nodup : literalKeys.Nodup := by decide

theorem sourceObservations_nodup : sourceObservations.Nodup := by
  apply List.Nodup.of_map observationKey
  rw [sourceObservations_keys]
  exact literalKeys_nodup

def sourceView (i : Fin 222) : Obs :=
  sourceObservations.get (Fin.cast sourceObservations_length.symm i)

theorem sourceView_injective : Function.Injective sourceView := by
  intro i j h
  have he := sourceObservations_nodup.injective_get h
  exact Fin.ext (congrArg Fin.val he)

theorem sourceView_bijective : Function.Bijective sourceView := by
  constructor
  · exact sourceView_injective
  · by_contra h
    have ht := Fintype.card_lt_of_injective_not_surjective sourceView sourceView_injective h
    rw [Fintype.card_fin, observation_card] at ht
    omega

noncomputable def sourceObservationEquiv : Fin 222 ≃ Obs :=
  Equiv.ofBijective sourceView sourceView_bijective

def literalColumns : List (Fin 255 × Fin 3) := [(⟨28, by decide⟩,⟨1, by decide⟩), (⟨29, by decide⟩,⟨0, by decide⟩), (⟨29, by decide⟩,⟨1, by decide⟩), (⟨30, by decide⟩,⟨0, by decide⟩), (⟨30, by decide⟩,⟨1, by decide⟩), (⟨31, by decide⟩,⟨0, by decide⟩), (⟨31, by decide⟩,⟨1, by decide⟩), (⟨32, by decide⟩,⟨0, by decide⟩), (⟨32, by decide⟩,⟨1, by decide⟩), (⟨33, by decide⟩,⟨0, by decide⟩), (⟨33, by decide⟩,⟨1, by decide⟩), (⟨34, by decide⟩,⟨0, by decide⟩), (⟨34, by decide⟩,⟨1, by decide⟩), (⟨35, by decide⟩,⟨0, by decide⟩), (⟨35, by decide⟩,⟨1, by decide⟩), (⟨36, by decide⟩,⟨0, by decide⟩), (⟨36, by decide⟩,⟨1, by decide⟩), (⟨37, by decide⟩,⟨0, by decide⟩), (⟨37, by decide⟩,⟨1, by decide⟩), (⟨38, by decide⟩,⟨0, by decide⟩), (⟨38, by decide⟩,⟨1, by decide⟩), (⟨39, by decide⟩,⟨0, by decide⟩), (⟨39, by decide⟩,⟨1, by decide⟩), (⟨40, by decide⟩,⟨0, by decide⟩), (⟨40, by decide⟩,⟨1, by decide⟩), (⟨41, by decide⟩,⟨0, by decide⟩), (⟨41, by decide⟩,⟨1, by decide⟩), (⟨42, by decide⟩,⟨0, by decide⟩), (⟨42, by decide⟩,⟨1, by decide⟩), (⟨43, by decide⟩,⟨0, by decide⟩), (⟨43, by decide⟩,⟨1, by decide⟩), (⟨44, by decide⟩,⟨0, by decide⟩), (⟨44, by decide⟩,⟨1, by decide⟩), (⟨45, by decide⟩,⟨0, by decide⟩), (⟨46, by decide⟩,⟨0, by decide⟩), (⟨47, by decide⟩,⟨1, by decide⟩), (⟨48, by decide⟩,⟨1, by decide⟩), (⟨49, by decide⟩,⟨0, by decide⟩), (⟨49, by decide⟩,⟨1, by decide⟩), (⟨50, by decide⟩,⟨0, by decide⟩), (⟨50, by decide⟩,⟨1, by decide⟩), (⟨51, by decide⟩,⟨0, by decide⟩), (⟨51, by decide⟩,⟨1, by decide⟩), (⟨52, by decide⟩,⟨0, by decide⟩), (⟨52, by decide⟩,⟨1, by decide⟩), (⟨53, by decide⟩,⟨0, by decide⟩), (⟨53, by decide⟩,⟨1, by decide⟩), (⟨54, by decide⟩,⟨0, by decide⟩), (⟨54, by decide⟩,⟨1, by decide⟩), (⟨55, by decide⟩,⟨0, by decide⟩), (⟨55, by decide⟩,⟨1, by decide⟩), (⟨56, by decide⟩,⟨0, by decide⟩), (⟨56, by decide⟩,⟨1, by decide⟩), (⟨57, by decide⟩,⟨0, by decide⟩), (⟨57, by decide⟩,⟨1, by decide⟩), (⟨58, by decide⟩,⟨0, by decide⟩), (⟨58, by decide⟩,⟨1, by decide⟩), (⟨59, by decide⟩,⟨0, by decide⟩), (⟨59, by decide⟩,⟨1, by decide⟩), (⟨60, by decide⟩,⟨0, by decide⟩), (⟨60, by decide⟩,⟨2, by decide⟩), (⟨61, by decide⟩,⟨0, by decide⟩), (⟨61, by decide⟩,⟨2, by decide⟩), (⟨62, by decide⟩,⟨0, by decide⟩), (⟨62, by decide⟩,⟨2, by decide⟩), (⟨63, by decide⟩,⟨0, by decide⟩), (⟨64, by decide⟩,⟨0, by decide⟩), (⟨64, by decide⟩,⟨2, by decide⟩), (⟨65, by decide⟩,⟨0, by decide⟩), (⟨65, by decide⟩,⟨2, by decide⟩), (⟨66, by decide⟩,⟨0, by decide⟩), (⟨66, by decide⟩,⟨2, by decide⟩), (⟨67, by decide⟩,⟨0, by decide⟩), (⟨67, by decide⟩,⟨2, by decide⟩), (⟨68, by decide⟩,⟨0, by decide⟩), (⟨68, by decide⟩,⟨2, by decide⟩), (⟨69, by decide⟩,⟨0, by decide⟩), (⟨69, by decide⟩,⟨2, by decide⟩), (⟨70, by decide⟩,⟨0, by decide⟩), (⟨70, by decide⟩,⟨2, by decide⟩), (⟨71, by decide⟩,⟨0, by decide⟩), (⟨71, by decide⟩,⟨2, by decide⟩), (⟨72, by decide⟩,⟨0, by decide⟩), (⟨72, by decide⟩,⟨2, by decide⟩), (⟨73, by decide⟩,⟨0, by decide⟩), (⟨73, by decide⟩,⟨2, by decide⟩), (⟨74, by decide⟩,⟨0, by decide⟩), (⟨74, by decide⟩,⟨2, by decide⟩), (⟨75, by decide⟩,⟨0, by decide⟩), (⟨75, by decide⟩,⟨2, by decide⟩), (⟨76, by decide⟩,⟨0, by decide⟩), (⟨76, by decide⟩,⟨2, by decide⟩), (⟨77, by decide⟩,⟨2, by decide⟩), (⟨78, by decide⟩,⟨0, by decide⟩), (⟨78, by decide⟩,⟨2, by decide⟩), (⟨79, by decide⟩,⟨0, by decide⟩), (⟨79, by decide⟩,⟨2, by decide⟩), (⟨80, by decide⟩,⟨0, by decide⟩), (⟨80, by decide⟩,⟨2, by decide⟩), (⟨81, by decide⟩,⟨0, by decide⟩), (⟨81, by decide⟩,⟨2, by decide⟩), (⟨82, by decide⟩,⟨0, by decide⟩), (⟨82, by decide⟩,⟨2, by decide⟩), (⟨83, by decide⟩,⟨0, by decide⟩), (⟨83, by decide⟩,⟨2, by decide⟩), (⟨84, by decide⟩,⟨0, by decide⟩), (⟨84, by decide⟩,⟨2, by decide⟩), (⟨85, by decide⟩,⟨0, by decide⟩), (⟨85, by decide⟩,⟨2, by decide⟩), (⟨86, by decide⟩,⟨0, by decide⟩), (⟨86, by decide⟩,⟨2, by decide⟩), (⟨87, by decide⟩,⟨0, by decide⟩), (⟨87, by decide⟩,⟨2, by decide⟩), (⟨88, by decide⟩,⟨0, by decide⟩), (⟨88, by decide⟩,⟨2, by decide⟩), (⟨89, by decide⟩,⟨0, by decide⟩), (⟨89, by decide⟩,⟨2, by decide⟩), (⟨90, by decide⟩,⟨0, by decide⟩), (⟨91, by decide⟩,⟨0, by decide⟩), (⟨91, by decide⟩,⟨2, by decide⟩), (⟨92, by decide⟩,⟨1, by decide⟩), (⟨93, by decide⟩,⟨0, by decide⟩), (⟨93, by decide⟩,⟨1, by decide⟩), (⟨94, by decide⟩,⟨0, by decide⟩), (⟨94, by decide⟩,⟨1, by decide⟩), (⟨95, by decide⟩,⟨0, by decide⟩), (⟨95, by decide⟩,⟨1, by decide⟩), (⟨124, by decide⟩,⟨2, by decide⟩), (⟨125, by decide⟩,⟨0, by decide⟩), (⟨125, by decide⟩,⟨2, by decide⟩), (⟨126, by decide⟩,⟨0, by decide⟩), (⟨126, by decide⟩,⟨2, by decide⟩), (⟨127, by decide⟩,⟨0, by decide⟩), (⟨127, by decide⟩,⟨2, by decide⟩), (⟨156, by decide⟩,⟨1, by decide⟩), (⟨157, by decide⟩,⟨0, by decide⟩), (⟨157, by decide⟩,⟨1, by decide⟩), (⟨158, by decide⟩,⟨0, by decide⟩), (⟨158, by decide⟩,⟨1, by decide⟩), (⟨159, by decide⟩,⟨0, by decide⟩), (⟨159, by decide⟩,⟨1, by decide⟩), (⟨159, by decide⟩,⟨2, by decide⟩), (⟨188, by decide⟩,⟨2, by decide⟩), (⟨189, by decide⟩,⟨0, by decide⟩), (⟨189, by decide⟩,⟨2, by decide⟩), (⟨190, by decide⟩,⟨0, by decide⟩), (⟨190, by decide⟩,⟨2, by decide⟩), (⟨191, by decide⟩,⟨0, by decide⟩), (⟨191, by decide⟩,⟨1, by decide⟩), (⟨220, by decide⟩,⟨1, by decide⟩), (⟨221, by decide⟩,⟨0, by decide⟩), (⟨221, by decide⟩,⟨1, by decide⟩), (⟨222, by decide⟩,⟨0, by decide⟩), (⟨222, by decide⟩,⟨1, by decide⟩), (⟨223, by decide⟩,⟨0, by decide⟩), (⟨223, by decide⟩,⟨1, by decide⟩), (⟨225, by decide⟩,⟨0, by decide⟩), (⟨225, by decide⟩,⟨1, by decide⟩), (⟨226, by decide⟩,⟨0, by decide⟩), (⟨226, by decide⟩,⟨1, by decide⟩), (⟨227, by decide⟩,⟨0, by decide⟩), (⟨227, by decide⟩,⟨1, by decide⟩), (⟨228, by decide⟩,⟨0, by decide⟩), (⟨228, by decide⟩,⟨1, by decide⟩), (⟨229, by decide⟩,⟨0, by decide⟩), (⟨229, by decide⟩,⟨1, by decide⟩), (⟨230, by decide⟩,⟨0, by decide⟩), (⟨230, by decide⟩,⟨1, by decide⟩), (⟨231, by decide⟩,⟨0, by decide⟩), (⟨231, by decide⟩,⟨1, by decide⟩), (⟨232, by decide⟩,⟨0, by decide⟩), (⟨232, by decide⟩,⟨1, by decide⟩), (⟨233, by decide⟩,⟨0, by decide⟩), (⟨233, by decide⟩,⟨1, by decide⟩), (⟨234, by decide⟩,⟨0, by decide⟩), (⟨234, by decide⟩,⟨1, by decide⟩), (⟨235, by decide⟩,⟨0, by decide⟩), (⟨235, by decide⟩,⟨1, by decide⟩), (⟨236, by decide⟩,⟨0, by decide⟩), (⟨237, by decide⟩,⟨0, by decide⟩), (⟨238, by decide⟩,⟨0, by decide⟩), (⟨238, by decide⟩,⟨1, by decide⟩), (⟨239, by decide⟩,⟨1, by decide⟩), (⟨240, by decide⟩,⟨0, by decide⟩), (⟨240, by decide⟩,⟨1, by decide⟩), (⟨241, by decide⟩,⟨0, by decide⟩), (⟨241, by decide⟩,⟨1, by decide⟩), (⟨242, by decide⟩,⟨0, by decide⟩), (⟨242, by decide⟩,⟨1, by decide⟩), (⟨243, by decide⟩,⟨0, by decide⟩), (⟨243, by decide⟩,⟨1, by decide⟩), (⟨244, by decide⟩,⟨0, by decide⟩), (⟨244, by decide⟩,⟨1, by decide⟩), (⟨245, by decide⟩,⟨0, by decide⟩), (⟨245, by decide⟩,⟨1, by decide⟩), (⟨246, by decide⟩,⟨0, by decide⟩), (⟨246, by decide⟩,⟨1, by decide⟩), (⟨247, by decide⟩,⟨0, by decide⟩), (⟨247, by decide⟩,⟨1, by decide⟩), (⟨248, by decide⟩,⟨0, by decide⟩), (⟨248, by decide⟩,⟨1, by decide⟩), (⟨249, by decide⟩,⟨0, by decide⟩), (⟨249, by decide⟩,⟨1, by decide⟩), (⟨250, by decide⟩,⟨0, by decide⟩), (⟨250, by decide⟩,⟨1, by decide⟩), (⟨251, by decide⟩,⟨0, by decide⟩), (⟨251, by decide⟩,⟨1, by decide⟩), (⟨252, by decide⟩,⟨0, by decide⟩), (⟨252, by decide⟩,⟨2, by decide⟩), (⟨253, by decide⟩,⟨0, by decide⟩), (⟨253, by decide⟩,⟨2, by decide⟩), (⟨254, by decide⟩,⟨0, by decide⟩), (⟨254, by decide⟩,⟨2, by decide⟩), (⟨254, by decide⟩,⟨1, by decide⟩), (⟨23, by decide⟩,⟨0, by decide⟩), (⟨23, by decide⟩,⟨1, by decide⟩), (⟨23, by decide⟩,⟨2, by decide⟩), (⟨24, by decide⟩,⟨0, by decide⟩), (⟨24, by decide⟩,⟨1, by decide⟩), (⟨24, by decide⟩,⟨2, by decide⟩), (⟨27, by decide⟩,⟨2, by decide⟩), (⟨47, by decide⟩,⟨2, by decide⟩)]
theorem literalColumns_length : literalColumns.length = 222 := rfl

def columnView (i : Fin 222) : Fin 255 × Fin 3 :=
  literalColumns.get (Fin.cast literalColumns_length.symm i)

theorem selectedColumns_sourceView (i : Fin 222) :
    selectedColumns (sourceView i) = columnView i := by
  fin_cases i
  case «0» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row0_selectedColumn
  case «1» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row1_selectedColumn
  case «2» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row2_selectedColumn
  case «3» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row3_selectedColumn
  case «4» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row4_selectedColumn
  case «5» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row5_selectedColumn
  case «6» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row6_selectedColumn
  case «7» => exact AspisV8R19.R790LiteralObservationOrderPrototype.row7_selectedColumn
  case «8» => exact AspisV8R19.R790LiteralObservationChunk00.row_008_selectedColumns
  case «9» => exact AspisV8R19.R790LiteralObservationChunk00.row_009_selectedColumns
  case «10» => exact AspisV8R19.R790LiteralObservationChunk00.row_010_selectedColumns
  case «11» => exact AspisV8R19.R790LiteralObservationChunk00.row_011_selectedColumns
  case «12» => exact AspisV8R19.R790LiteralObservationChunk00.row_012_selectedColumns
  case «13» => exact AspisV8R19.R790LiteralObservationChunk00.row_013_selectedColumns
  case «14» => exact AspisV8R19.R790LiteralObservationChunk00.row_014_selectedColumns
  case «15» => exact AspisV8R19.R790LiteralObservationChunk00.row_015_selectedColumns
  case «16» => exact AspisV8R19.R790LiteralObservationChunk00.row_016_selectedColumns
  case «17» => exact AspisV8R19.R790LiteralObservationChunk00.row_017_selectedColumns
  case «18» => exact AspisV8R19.R790LiteralObservationChunk00.row_018_selectedColumns
  case «19» => exact AspisV8R19.R790LiteralObservationChunk00.row_019_selectedColumns
  case «20» => exact AspisV8R19.R790LiteralObservationChunk00.row_020_selectedColumns
  case «21» => exact AspisV8R19.R790LiteralObservationChunk00.row_021_selectedColumns
  case «22» => exact AspisV8R19.R790LiteralObservationChunk00.row_022_selectedColumns
  case «23» => exact AspisV8R19.R790LiteralObservationChunk00.row_023_selectedColumns
  case «24» => exact AspisV8R19.R790LiteralObservationChunk01.row_024_selectedColumns
  case «25» => exact AspisV8R19.R790LiteralObservationChunk01.row_025_selectedColumns
  case «26» => exact AspisV8R19.R790LiteralObservationChunk01.row_026_selectedColumns
  case «27» => exact AspisV8R19.R790LiteralObservationChunk01.row_027_selectedColumns
  case «28» => exact AspisV8R19.R790LiteralObservationChunk01.row_028_selectedColumns
  case «29» => exact AspisV8R19.R790LiteralObservationChunk01.row_029_selectedColumns
  case «30» => exact AspisV8R19.R790LiteralObservationChunk01.row_030_selectedColumns
  case «31» => exact AspisV8R19.R790LiteralObservationChunk01.row_031_selectedColumns
  case «32» => exact AspisV8R19.R790LiteralObservationChunk01.row_032_selectedColumns
  case «33» => exact AspisV8R19.R790LiteralObservationChunk01.row_033_selectedColumns
  case «34» => exact AspisV8R19.R790LiteralObservationChunk01.row_034_selectedColumns
  case «35» => exact AspisV8R19.R790LiteralObservationChunk01.row_035_selectedColumns
  case «36» => exact AspisV8R19.R790LiteralObservationChunk01.row_036_selectedColumns
  case «37» => exact AspisV8R19.R790LiteralObservationChunk01.row_037_selectedColumns
  case «38» => exact AspisV8R19.R790LiteralObservationChunk01.row_038_selectedColumns
  case «39» => exact AspisV8R19.R790LiteralObservationChunk01.row_039_selectedColumns
  case «40» => exact AspisV8R19.R790LiteralObservationChunk02.row_040_selectedColumns
  case «41» => exact AspisV8R19.R790LiteralObservationChunk02.row_041_selectedColumns
  case «42» => exact AspisV8R19.R790LiteralObservationChunk02.row_042_selectedColumns
  case «43» => exact AspisV8R19.R790LiteralObservationChunk02.row_043_selectedColumns
  case «44» => exact AspisV8R19.R790LiteralObservationChunk02.row_044_selectedColumns
  case «45» => exact AspisV8R19.R790LiteralObservationChunk02.row_045_selectedColumns
  case «46» => exact AspisV8R19.R790LiteralObservationChunk02.row_046_selectedColumns
  case «47» => exact AspisV8R19.R790LiteralObservationChunk02.row_047_selectedColumns
  case «48» => exact AspisV8R19.R790LiteralObservationChunk02.row_048_selectedColumns
  case «49» => exact AspisV8R19.R790LiteralObservationChunk02.row_049_selectedColumns
  case «50» => exact AspisV8R19.R790LiteralObservationChunk02.row_050_selectedColumns
  case «51» => exact AspisV8R19.R790LiteralObservationChunk02.row_051_selectedColumns
  case «52» => exact AspisV8R19.R790LiteralObservationChunk02.row_052_selectedColumns
  case «53» => exact AspisV8R19.R790LiteralObservationChunk02.row_053_selectedColumns
  case «54» => exact AspisV8R19.R790LiteralObservationChunk02.row_054_selectedColumns
  case «55» => exact AspisV8R19.R790LiteralObservationChunk02.row_055_selectedColumns
  case «56» => exact AspisV8R19.R790LiteralObservationChunk03.row_056_selectedColumns
  case «57» => exact AspisV8R19.R790LiteralObservationChunk03.row_057_selectedColumns
  case «58» => exact AspisV8R19.R790LiteralObservationChunk03.row_058_selectedColumns
  case «59» => exact AspisV8R19.R790LiteralObservationChunk03.row_059_selectedColumns
  case «60» => exact AspisV8R19.R790LiteralObservationChunk03.row_060_selectedColumns
  case «61» => exact AspisV8R19.R790LiteralObservationChunk03.row_061_selectedColumns
  case «62» => exact AspisV8R19.R790LiteralObservationChunk03.row_062_selectedColumns
  case «63» => exact AspisV8R19.R790LiteralObservationChunk03.row_063_selectedColumns
  case «64» => exact AspisV8R19.R790LiteralObservationChunk03.row_064_selectedColumns
  case «65» => exact AspisV8R19.R790LiteralObservationChunk03.row_065_selectedColumns
  case «66» => exact AspisV8R19.R790LiteralObservationChunk03.row_066_selectedColumns
  case «67» => exact AspisV8R19.R790LiteralObservationChunk03.row_067_selectedColumns
  case «68» => exact AspisV8R19.R790LiteralObservationChunk03.row_068_selectedColumns
  case «69» => exact AspisV8R19.R790LiteralObservationChunk03.row_069_selectedColumns
  case «70» => exact AspisV8R19.R790LiteralObservationChunk03.row_070_selectedColumns
  case «71» => exact AspisV8R19.R790LiteralObservationChunk03.row_071_selectedColumns
  case «72» => exact AspisV8R19.R790LiteralObservationChunk04.row_072_selectedColumns
  case «73» => exact AspisV8R19.R790LiteralObservationChunk04.row_073_selectedColumns
  case «74» => exact AspisV8R19.R790LiteralObservationChunk04.row_074_selectedColumns
  case «75» => exact AspisV8R19.R790LiteralObservationChunk04.row_075_selectedColumns
  case «76» => exact AspisV8R19.R790LiteralObservationChunk04.row_076_selectedColumns
  case «77» => exact AspisV8R19.R790LiteralObservationChunk04.row_077_selectedColumns
  case «78» => exact AspisV8R19.R790LiteralObservationChunk04.row_078_selectedColumns
  case «79» => exact AspisV8R19.R790LiteralObservationChunk04.row_079_selectedColumns
  case «80» => exact AspisV8R19.R790LiteralObservationChunk04.row_080_selectedColumns
  case «81» => exact AspisV8R19.R790LiteralObservationChunk04.row_081_selectedColumns
  case «82» => exact AspisV8R19.R790LiteralObservationChunk04.row_082_selectedColumns
  case «83» => exact AspisV8R19.R790LiteralObservationChunk04.row_083_selectedColumns
  case «84» => exact AspisV8R19.R790LiteralObservationChunk04.row_084_selectedColumns
  case «85» => exact AspisV8R19.R790LiteralObservationChunk04.row_085_selectedColumns
  case «86» => exact AspisV8R19.R790LiteralObservationChunk04.row_086_selectedColumns
  case «87» => exact AspisV8R19.R790LiteralObservationChunk04.row_087_selectedColumns
  case «88» => exact AspisV8R19.R790LiteralObservationChunk05.row_088_selectedColumns
  case «89» => exact AspisV8R19.R790LiteralObservationChunk05.row_089_selectedColumns
  case «90» => exact AspisV8R19.R790LiteralObservationChunk05.row_090_selectedColumns
  case «91» => exact AspisV8R19.R790LiteralObservationChunk05.row_091_selectedColumns
  case «92» => exact AspisV8R19.R790LiteralObservationChunk05.row_092_selectedColumns
  case «93» => exact AspisV8R19.R790LiteralObservationChunk05.row_093_selectedColumns
  case «94» => exact AspisV8R19.R790LiteralObservationChunk05.row_094_selectedColumns
  case «95» => exact AspisV8R19.R790LiteralObservationChunk05.row_095_selectedColumns
  case «96» => exact AspisV8R19.R790LiteralObservationChunk05.row_096_selectedColumns
  case «97» => exact AspisV8R19.R790LiteralObservationChunk05.row_097_selectedColumns
  case «98» => exact AspisV8R19.R790LiteralObservationChunk05.row_098_selectedColumns
  case «99» => exact AspisV8R19.R790LiteralObservationChunk05.row_099_selectedColumns
  case «100» => exact AspisV8R19.R790LiteralObservationChunk05.row_100_selectedColumns
  case «101» => exact AspisV8R19.R790LiteralObservationChunk05.row_101_selectedColumns
  case «102» => exact AspisV8R19.R790LiteralObservationChunk05.row_102_selectedColumns
  case «103» => exact AspisV8R19.R790LiteralObservationChunk05.row_103_selectedColumns
  case «104» => exact AspisV8R19.R790LiteralObservationChunk06.row_104_selectedColumns
  case «105» => exact AspisV8R19.R790LiteralObservationChunk06.row_105_selectedColumns
  case «106» => exact AspisV8R19.R790LiteralObservationChunk06.row_106_selectedColumns
  case «107» => exact AspisV8R19.R790LiteralObservationChunk06.row_107_selectedColumns
  case «108» => exact AspisV8R19.R790LiteralObservationChunk06.row_108_selectedColumns
  case «109» => exact AspisV8R19.R790LiteralObservationChunk06.row_109_selectedColumns
  case «110» => exact AspisV8R19.R790LiteralObservationChunk06.row_110_selectedColumns
  case «111» => exact AspisV8R19.R790LiteralObservationChunk06.row_111_selectedColumns
  case «112» => exact AspisV8R19.R790LiteralObservationChunk06.row_112_selectedColumns
  case «113» => exact AspisV8R19.R790LiteralObservationChunk06.row_113_selectedColumns
  case «114» => exact AspisV8R19.R790LiteralObservationChunk06.row_114_selectedColumns
  case «115» => exact AspisV8R19.R790LiteralObservationChunk06.row_115_selectedColumns
  case «116» => exact AspisV8R19.R790LiteralObservationChunk06.row_116_selectedColumns
  case «117» => exact AspisV8R19.R790LiteralObservationChunk06.row_117_selectedColumns
  case «118» => exact AspisV8R19.R790LiteralObservationChunk06.row_118_selectedColumns
  case «119» => exact AspisV8R19.R790LiteralObservationChunk06.row_119_selectedColumns
  case «120» => exact AspisV8R19.R790LiteralObservationChunk07.row_120_selectedColumns
  case «121» => exact AspisV8R19.R790LiteralObservationChunk07.row_121_selectedColumns
  case «122» => exact AspisV8R19.R790LiteralObservationChunk07.row_122_selectedColumns
  case «123» => exact AspisV8R19.R790LiteralObservationChunk07.row_123_selectedColumns
  case «124» => exact AspisV8R19.R790LiteralObservationChunk07.row_124_selectedColumns
  case «125» => exact AspisV8R19.R790LiteralObservationChunk07.row_125_selectedColumns
  case «126» => exact AspisV8R19.R790LiteralObservationChunk07.row_126_selectedColumns
  case «127» => exact AspisV8R19.R790LiteralObservationChunk07.row_127_selectedColumns
  case «128» => exact AspisV8R19.R790LiteralObservationChunk07.row_128_selectedColumns
  case «129» => exact AspisV8R19.R790LiteralObservationChunk07.row_129_selectedColumns
  case «130» => exact AspisV8R19.R790LiteralObservationChunk07.row_130_selectedColumns
  case «131» => exact AspisV8R19.R790LiteralObservationChunk07.row_131_selectedColumns
  case «132» => exact AspisV8R19.R790LiteralObservationChunk07.row_132_selectedColumns
  case «133» => exact AspisV8R19.R790LiteralObservationChunk07.row_133_selectedColumns
  case «134» => exact AspisV8R19.R790LiteralObservationChunk07.row_134_selectedColumns
  case «135» => exact AspisV8R19.R790LiteralObservationChunk07.row_135_selectedColumns
  case «136» => exact AspisV8R19.R790LiteralObservationChunk08.row_136_selectedColumns
  case «137» => exact AspisV8R19.R790LiteralObservationChunk08.row_137_selectedColumns
  case «138» => exact AspisV8R19.R790LiteralObservationChunk08.row_138_selectedColumns
  case «139» => exact AspisV8R19.R790LiteralObservationChunk08.row_139_selectedColumns
  case «140» => exact AspisV8R19.R790LiteralObservationChunk08.row_140_selectedColumns
  case «141» => exact AspisV8R19.R790LiteralObservationChunk08.row_141_selectedColumns
  case «142» => exact AspisV8R19.R790LiteralObservationChunk08.row_142_selectedColumns
  case «143» => exact AspisV8R19.R790LiteralObservationChunk08.row_143_selectedColumns
  case «144» => exact AspisV8R19.R790LiteralObservationChunk08.row_144_selectedColumns
  case «145» => exact AspisV8R19.R790LiteralObservationChunk08.row_145_selectedColumns
  case «146» => exact AspisV8R19.R790LiteralObservationChunk08.row_146_selectedColumns
  case «147» => exact AspisV8R19.R790LiteralObservationChunk08.row_147_selectedColumns
  case «148» => exact AspisV8R19.R790LiteralObservationChunk08.row_148_selectedColumns
  case «149» => exact AspisV8R19.R790LiteralObservationChunk08.row_149_selectedColumns
  case «150» => exact AspisV8R19.R790LiteralObservationChunk08.row_150_selectedColumns
  case «151» => exact AspisV8R19.R790LiteralObservationChunk08.row_151_selectedColumns
  case «152» => exact AspisV8R19.R790LiteralObservationChunk09.row_152_selectedColumns
  case «153» => exact AspisV8R19.R790LiteralObservationChunk09.row_153_selectedColumns
  case «154» => exact AspisV8R19.R790LiteralObservationChunk09.row_154_selectedColumns
  case «155» => exact AspisV8R19.R790LiteralObservationChunk09.row_155_selectedColumns
  case «156» => exact AspisV8R19.R790LiteralObservationChunk09.row_156_selectedColumns
  case «157» => exact AspisV8R19.R790LiteralObservationChunk09.row_157_selectedColumns
  case «158» => exact AspisV8R19.R790LiteralObservationChunk09.row_158_selectedColumns
  case «159» => exact AspisV8R19.R790LiteralObservationChunk09.row_159_selectedColumns
  case «160» => exact AspisV8R19.R790LiteralObservationChunk09.row_160_selectedColumns
  case «161» => exact AspisV8R19.R790LiteralObservationChunk09.row_161_selectedColumns
  case «162» => exact AspisV8R19.R790LiteralObservationChunk09.row_162_selectedColumns
  case «163» => exact AspisV8R19.R790LiteralObservationChunk09.row_163_selectedColumns
  case «164» => exact AspisV8R19.R790LiteralObservationChunk09.row_164_selectedColumns
  case «165» => exact AspisV8R19.R790LiteralObservationChunk09.row_165_selectedColumns
  case «166» => exact AspisV8R19.R790LiteralObservationChunk09.row_166_selectedColumns
  case «167» => exact AspisV8R19.R790LiteralObservationChunk09.row_167_selectedColumns
  case «168» => exact AspisV8R19.R790LiteralObservationChunk10.row_168_selectedColumns
  case «169» => exact AspisV8R19.R790LiteralObservationChunk10.row_169_selectedColumns
  case «170» => exact AspisV8R19.R790LiteralObservationChunk10.row_170_selectedColumns
  case «171» => exact AspisV8R19.R790LiteralObservationChunk10.row_171_selectedColumns
  case «172» => exact AspisV8R19.R790LiteralObservationChunk10.row_172_selectedColumns
  case «173» => exact AspisV8R19.R790LiteralObservationChunk10.row_173_selectedColumns
  case «174» => exact AspisV8R19.R790LiteralObservationChunk10.row_174_selectedColumns
  case «175» => exact AspisV8R19.R790LiteralObservationChunk10.row_175_selectedColumns
  case «176» => exact AspisV8R19.R790LiteralObservationChunk10.row_176_selectedColumns
  case «177» => exact AspisV8R19.R790LiteralObservationChunk10.row_177_selectedColumns
  case «178» => exact AspisV8R19.R790LiteralObservationChunk10.row_178_selectedColumns
  case «179» => exact AspisV8R19.R790LiteralObservationChunk10.row_179_selectedColumns
  case «180» => exact AspisV8R19.R790LiteralObservationChunk10.row_180_selectedColumns
  case «181» => exact AspisV8R19.R790LiteralObservationChunk10.row_181_selectedColumns
  case «182» => exact AspisV8R19.R790LiteralObservationChunk10.row_182_selectedColumns
  case «183» => exact AspisV8R19.R790LiteralObservationChunk10.row_183_selectedColumns
  case «184» => exact AspisV8R19.R790LiteralObservationChunk11.row_184_selectedColumns
  case «185» => exact AspisV8R19.R790LiteralObservationChunk11.row_185_selectedColumns
  case «186» => exact AspisV8R19.R790LiteralObservationChunk11.row_186_selectedColumns
  case «187» => exact AspisV8R19.R790LiteralObservationChunk11.row_187_selectedColumns
  case «188» => exact AspisV8R19.R790LiteralObservationChunk11.row_188_selectedColumns
  case «189» => exact AspisV8R19.R790LiteralObservationChunk11.row_189_selectedColumns
  case «190» => exact AspisV8R19.R790LiteralObservationChunk11.row_190_selectedColumns
  case «191» => exact AspisV8R19.R790LiteralObservationChunk11.row_191_selectedColumns
  case «192» => exact AspisV8R19.R790LiteralObservationChunk11.row_192_selectedColumns
  case «193» => exact AspisV8R19.R790LiteralObservationChunk11.row_193_selectedColumns
  case «194» => exact AspisV8R19.R790LiteralObservationChunk11.row_194_selectedColumns
  case «195» => exact AspisV8R19.R790LiteralObservationChunk11.row_195_selectedColumns
  case «196» => exact AspisV8R19.R790LiteralObservationChunk11.row_196_selectedColumns
  case «197» => exact AspisV8R19.R790LiteralObservationChunk11.row_197_selectedColumns
  case «198» => exact AspisV8R19.R790LiteralObservationChunk11.row_198_selectedColumns
  case «199» => exact AspisV8R19.R790LiteralObservationChunk11.row_199_selectedColumns
  case «200» => exact AspisV8R19.R790LiteralObservationChunk12.row_200_selectedColumns
  case «201» => exact AspisV8R19.R790LiteralObservationChunk12.row_201_selectedColumns
  case «202» => exact AspisV8R19.R790LiteralObservationChunk12.row_202_selectedColumns
  case «203» => exact AspisV8R19.R790LiteralObservationChunk12.row_203_selectedColumns
  case «204» => exact AspisV8R19.R790LiteralObservationChunk12.row_204_selectedColumns
  case «205» => exact AspisV8R19.R790LiteralObservationChunk12.row_205_selectedColumns
  case «206» => exact AspisV8R19.R790LiteralObservationChunk12.row_206_selectedColumns
  case «207» => exact AspisV8R19.R790LiteralObservationChunk12.row_207_selectedColumns
  case «208» => exact AspisV8R19.R790LiteralObservationChunk12.row_208_selectedColumns
  case «209» => exact AspisV8R19.R790LiteralObservationChunk12.row_209_selectedColumns
  case «210» => exact AspisV8R19.R790LiteralObservationChunk12.row_210_selectedColumns
  case «211» => exact AspisV8R19.R790LiteralObservationChunk12.row_211_selectedColumns
  case «212» => exact AspisV8R19.R790LiteralObservationChunk12.row_212_selectedColumns
  case «213» => exact AspisV8R19.R790LiteralObservationChunk12.top_selectedColumns
  case «214» => exact AspisV8R19.R790LiteralObservationChunk12.point_0_selectedColumns
  case «215» => exact AspisV8R19.R790LiteralObservationChunk12.point_1_selectedColumns
  case «216» => exact AspisV8R19.R790LiteralObservationChunk13.point_2_selectedColumns
  case «217» => exact AspisV8R19.R790LiteralObservationChunk13.coeff_0_selectedColumns
  case «218» => exact AspisV8R19.R790LiteralObservationChunk13.coeff_1_selectedColumns
  case «219» => exact AspisV8R19.R790LiteralObservationChunk13.coeff_2_selectedColumns
  case «220» => exact AspisV8R19.R790LiteralObservationChunk13.coeff_3_selectedColumns
  case «221» => exact AspisV8R19.R790LiteralObservationChunk13.coeff_4_selectedColumns

#print axioms sourceObservations_length
#print axioms sourceObservations_keys
#print axioms literalKeys_nodup
#print axioms sourceObservations_nodup
#print axioms sourceView_injective
#print axioms sourceView_bijective
#print axioms sourceObservationEquiv
#print axioms literalColumns_length
#print axioms selectedColumns_sourceView
end AspisV8R19.R798LiteralObservationView
