import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots4
import NDO_JGw_Circle4
import NDO_JGw_Values4
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle4
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value04_3.value
def d0 : FE := ⟨⟨⟨248068782,875494695⟩,⟨1255231373,1306862877⟩⟩,⟨⟨2136045275,1239930110⟩,⟨224918844,2017869355⟩⟩⟩
def h0 : FE := ⟨⟨⟨1048240648,1517690011⟩,⟨1201363879,520292516⟩⟩,⟨⟨30851749,1208014354⟩,⟨2082558982,1945126577⟩⟩⟩
def d1 : FE := ⟨⟨⟨988444794,337131938⟩,⟨511489315,860404759⟩⟩,⟨⟨1451223432,1658110460⟩,⟨256252699,1358443403⟩⟩⟩
def h1 : FE := ⟨⟨⟨447793929,2044136379⟩,⟨2108546978,1119014759⟩⟩,⟨⟨253239572,141932763⟩,⟨790053285,47905688⟩⟩⟩
def d2 : FE := ⟨⟨⟨843289301,377020022⟩,⟨2071691786,592886191⟩⟩,⟨⟨2049772026,1564388390⟩,⟨1687722914,855145008⟩⟩⟩
def h2 : FE := ⟨⟨⟨1818617691,1668892097⟩,⟨911387977,11732555⟩⟩,⟨⟨1805062701,1675979897⟩,⟨1953978870,2038323509⟩⟩⟩
def d3 : FE := ⟨⟨⟨2113159715,186146095⟩,⟨967043042,1468499884⟩⟩,⟨⟨928817204,369628456⟩,⟨1866374177,1401564895⟩⟩⟩
def h3 : FE := ⟨⟨⟨668160825,1350785778⟩,⟨103001672,1221709778⟩⟩,⟨⟨1799041958,1991708919⟩,⟨2092745021,1428420744⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨174453424,1533326757⟩,⟨1099354401,1238807955⟩⟩,⟨⟨1959926972,761144675⟩,⟨632817477,2067086775⟩⟩⟩
def t1 : FE := ⟨⟨⟨1141987806,876813483⟩,⟨953940760,2032717673⟩⟩,⟨⟨1370136257,1417758682⟩,⟨1409850976,1848182036⟩⟩⟩
def value : FE := ⟨⟨⟨1733495406,1006483110⟩,⟨1825086166,254379937⟩⟩,⟨⟨2096922458,1310138954⟩,⟨1695658189,716103946⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 4).x)⁻¹=(870373892 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 590827366 870373892 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 4).y)⁻¹=(803870471 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 907826580 803870471 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*803870471)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*870373892)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*870373892*803870471)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 870373892)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 803870471)
    (Port5Q1_OpeningValues.values JHa_Dots4.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 870373892=(870373892:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 803870471=(803870471:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots4.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots4.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots4.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots4.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots4.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 4)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle4.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots4.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1733495406<2147483647 ∧ 1006483110<2147483647) ∧ (1825086166<2147483647 ∧ 254379937<2147483647)) ∧
      ((2096922458<2147483647 ∧ 1310138954<2147483647) ∧ (1695658189<2147483647 ∧ 716103946<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle4
end
