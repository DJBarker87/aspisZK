import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots6
import NDO_JGw_Circle6
import NDO_JGw_Values6
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle6
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value06_1.value
def d0 : FE := ⟨⟨⟨340496462,927013527⟩,⟨409577040,1265424778⟩⟩,⟨⟨1024733769,1837115435⟩,⟨1347457310,103842217⟩⟩⟩
def h0 : FE := ⟨⟨⟨1093845429,291138268⟩,⟨1742075661,354075858⟩⟩,⟨⟨1734458911,1069366814⟩,⟨2020782692,1168928628⟩⟩⟩
def d1 : FE := ⟨⟨⟨355291408,515929680⟩,⟨1611022204,329031969⟩⟩,⟨⟨1088386878,339553167⟩,⟨1007157258,1125622910⟩⟩⟩
def h1 : FE := ⟨⟨⟨1062493315,882706345⟩,⟨2091405567,1529284764⟩⟩,⟨⟨255018984,1172902943⟩,⟨306337065,1757055974⟩⟩⟩
def d2 : FE := ⟨⟨⟨726189189,1954132106⟩,⟨508877039,1796746750⟩⟩,⟨⟨561074169,618403246⟩,⟨1333634584,1116054999⟩⟩⟩
def h2 : FE := ⟨⟨⟨556017932,1865133923⟩,⟨266917015,1316061898⟩⟩,⟨⟨1718156042,1852275857⟩,⟨1777823150,816059346⟩⟩⟩
def d3 : FE := ⟨⟨⟨805921010,2062445053⟩,⟨143859067,172583582⟩⟩,⟨⟨2116157181,1482395408⟩,⟨99914322,182710739⟩⟩⟩
def h3 : FE := ⟨⟨⟨1582026480,2035512310⟩,⟨1716222673,1898604406⟩⟩,⟨⟨193607526,495852028⟩,⟨1060711674,1006329649⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨1063348655,1129521854⟩,⟨262638168,551726749⟩⟩,⟨⟨1322381339,859511794⟩,⟨1022555795,1634544707⟩⟩⟩
def t1 : FE := ⟨⟨⟨717515558,1870204045⟩,⟨548370827,1662896668⟩⟩,⟨⟨1529250146,1083649229⟩,⟨910468563,654824268⟩⟩⟩
def value : FE := ⟨⟨⟨1396410589,253103824⟩,⟨812667064,1952677907⟩⟩,⟨⟨422301239,1782981050⟩,⟨462977955,1206238169⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 6).x)⁻¹=(573474238 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 156224156 573474238 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 6).y)⁻¹=(967362338 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1027182117 967362338 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*967362338)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*573474238)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*573474238*967362338)=h3 := by
  unfold d0 d1 d2 d3 h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient3
theorem horner2 : h2+alpha*h3=t2 := by
  unfold h2 alpha h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner2
theorem horner1 : h1+alpha*t2=t1 := by
  unfold h1 alpha t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner1
theorem horner0 : h0+alpha*t1=value := by
  unfold h0 alpha t1 value
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner0
theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 573474238)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 967362338)
    (Port5Q1_OpeningValues.values JHa_Dots6.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 573474238=(573474238:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 967362338=(967362338:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots6.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots6.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots6.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots6.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots6.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 6)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle6.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots6.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1396410589<2147483647 ∧ 253103824<2147483647) ∧ (812667064<2147483647 ∧ 1952677907<2147483647)) ∧
      ((422301239<2147483647 ∧ 1782981050<2147483647) ∧ (462977955<2147483647 ∧ 1206238169<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle6
end
