import NDO_JGd_Coefficient25
import NDO_JGd_LinearValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficients
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe JGd_CoefficientData JGd_ExactWords

theorem loop0 : ExtractedMaskCoefficientLoop0.writeModel0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
    ExtractedMaskCallerModel.initialCoefficients ExtractedMaskCallerModel.range0 16 = a16 := by
  unfold ExtractedMaskCallerModel.initialCoefficients field.QM31.ZERO
  unfold ExtractedMaskCallerModel.range0 state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS
  change ExtractedMaskCoefficientLoop0.writeModel0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a00 ⟨0#usize,16#usize⟩ 16 = a16
  rw [JGd_Coefficient00.advance,JGd_Coefficient01.advance,JGd_Coefficient02.advance,JGd_Coefficient03.advance,JGd_Coefficient04.advance,JGd_Coefficient05.advance,JGd_Coefficient06.advance,JGd_Coefficient07.advance,JGd_Coefficient08.advance,JGd_Coefficient09.advance,JGd_Coefficient10.advance,JGd_Coefficient11.advance,JGd_Coefficient12.advance,JGd_Coefficient13.advance,JGd_Coefficient14.advance,JGd_Coefficient15.advance]
  rfl
#print axioms loop0

theorem loop1 : ExtractedMaskCoefficientLoop1.writeModel1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
    a16 ExtractedMaskCallerModel.range1 10 = a26 := by
  unfold ExtractedMaskCallerModel.range1 state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  rw [JGd_Coefficient16.advance,JGd_Coefficient17.advance,JGd_Coefficient18.advance,JGd_Coefficient19.advance,JGd_Coefficient20.advance,JGd_Coefficient21.advance,JGd_Coefficient22.advance,JGd_Coefficient23.advance,JGd_Coefficient24.advance,JGd_Coefficient25.advance]
  rfl
#print axioms loop1

theorem populated : ExtractedMaskCallerModel.populatedCoefficients
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) = a26 := by
  unfold ExtractedMaskCallerModel.populatedCoefficients
  rw [loop0,loop1]
#print axioms populated
def words : Array W 27#usize := ⟨[((1262673698,1732185580),(1505713530,598598498)),((479557376,317941656),(305958949,1440737655)),((618372131,122159246),(256739982,1799434707)),((263885395,1156423977),(69557710,1752370157)),((728529646,1663927709),(598058443,361803088)),((1096117093,1130606432),(382077289,1383986122)),((1434898007,868692877),(202236232,1592384557)),((1740660488,941111058),(1379313910,156420109)),((652624296,575674261),(1739907054,2128745497)),((1739440629,614011834),(7009573,1034581171)),((713672305,261001302),(351876930,2093232551)),((1299655517,2041608749),(456406906,1698118915)),((1817042326,602175684),(1519785285,417843121)),((283029589,239090374),(880136653,1071546159)),((1413048506,650264934),(330782163,844088711)),((36145286,671015250),(1819985108,1775297862)),((1758460621,1711624258),(1933517417,1591239394)),((1314215867,1323872981),(187458889,576030860)),((129937185,1783465304),(1878418167,1885178356)),((40105540,1572894176),(1128859828,1452095554)),((1243155426,313918335),(1349681398,213500445)),((1005878124,31707117),(1471984256,1555692882)),((1041660409,2084682198),(127997613,111471460)),((0,0),(0,0)),((1389564877,490792350),(498007426,530169430)),((935552911,1268906353),(456913005,1928970014)),((1794094306,970136214),(692219080,662936248))],by rfl⟩
def cell (i : Fin 27) : W := words.val[i.val]'(by simpa [words.property] using i.isLt)
theorem value (i : Fin 27) : ExtractedMaskHornerCaller.coefficientValue
    (ExtractedMaskCallerModel.populatedCoefficients
      (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)) i.val = JGd_ExactWords.value (cell i) := by
  rw [populated]
  fin_cases i <;> rfl
#print axioms value
end AspisR1.JGd_Coefficients
end
