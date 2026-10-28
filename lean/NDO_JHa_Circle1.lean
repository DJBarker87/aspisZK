import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots1
import NDO_JGw_Circle1
import NDO_JGw_Values1
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle1
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value01_1.value
def d0 : FE := ⟨⟨⟨1104294386,720857587⟩,⟨966575011,1698589277⟩⟩,⟨⟨720244953,1915033055⟩,⟨634508911,900318784⟩⟩⟩
def h0 : FE := ⟨⟨⟨1479767421,813358567⟩,⟨1849715772,1185229976⟩⟩,⟨⟨166779479,1309627885⟩,⟨401657670,1906383946⟩⟩⟩
def d1 : FE := ⟨⟨⟨501674758,951393984⟩,⟨847048177,1362634893⟩⟩,⟨⟨43023868,1775050685⟩,⟨79695355,499948639⟩⟩⟩
def h1 : FE := ⟨⟨⟨704796695,1554452973⟩,⟨1610357848,1774408244⟩⟩,⟨⟨719572338,234558541⟩,⟨1135124487,753965275⟩⟩⟩
def d2 : FE := ⟨⟨⟨2104605253,1630266283⟩,⟨528303231,1979137618⟩⟩,⟨⟨1696048404,1857837136⟩,⟨819312160,116723867⟩⟩⟩
def h2 : FE := ⟨⟨⟨990237454,1621775182⟩,⟨1171234344,1636234224⟩⟩,⟨⟨788972112,1761658286⟩,⟨791908821,825474880⟩⟩⟩
def d3 : FE := ⟨⟨⟨61011640,2098400061⟩,⟨761969375,1848041763⟩⟩,⟨⟨355284338,1838074311⟩,⟨73114254,1813577200⟩⟩⟩
def h3 : FE := ⟨⟨⟨268838312,1992647687⟩,⟨1252916569,809627433⟩⟩,⟨⟨402214222,1233136031⟩,⟨997630461,1706278436⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨1239464663,81358206⟩,⟨1313948386,1115801334⟩⟩,⟨⟨1344260458,973128197⟩,⟨1570366102,250401101⟩⟩⟩
def t1 : FE := ⟨⟨⟨1088055120,1035305473⟩,⟨1373941455,330193548⟩⟩,⟨⟨289697202,409053020⟩,⟨2141643342,367183888⟩⟩⟩
def value : FE := ⟨⟨⟨3946788,1921141621⟩,⟨1912846855,81146261⟩⟩,⟨⟨944397719,1465743260⟩,⟨691618691,1876781494⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 1).x)⁻¹=(527485689 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 294074545 527485689 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 1).y)⁻¹=(1562835950 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1230260130 1562835950 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1562835950)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*527485689)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*527485689*1562835950)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 527485689)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1562835950)
    (Port5Q1_OpeningValues.values JHa_Dots1.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 527485689=(527485689:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1562835950=(1562835950:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots1.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots1.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots1.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots1.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots1.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 1)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle1.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots1.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((3946788<2147483647 ∧ 1921141621<2147483647) ∧ (1912846855<2147483647 ∧ 81146261<2147483647)) ∧
      ((944397719<2147483647 ∧ 1465743260<2147483647) ∧ (691618691<2147483647 ∧ 1876781494<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle1
end
