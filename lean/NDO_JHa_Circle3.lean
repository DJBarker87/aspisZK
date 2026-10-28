import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots3
import NDO_JGw_Circle3
import NDO_JGw_Values3
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle3
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value03_3.value
def d0 : FE := ⟨⟨⟨1378643633,1998300647⟩,⟨1303355456,504658715⟩⟩,⟨⟨1395440008,844315861⟩,⟨1494641892,1110651981⟩⟩⟩
def h0 : FE := ⟨⟨⟨1197815850,1620237230⟩,⟨608185590,1958587220⟩⟩,⟨⟨1111657479,624681948⟩,⟨1545756881,784336579⟩⟩⟩
def d1 : FE := ⟨⟨⟨672286286,1432112492⟩,⟨771518612,1902903684⟩⟩,⟨⟨2022515589,216190726⟩,⟨977464792,559433199⟩⟩⟩
def h1 : FE := ⟨⟨⟨384045652,1387707286⟩,⟨1405313486,203723467⟩⟩,⟨⟨1011565981,460646396⟩,⟨55381547,1467576082⟩⟩⟩
def d2 : FE := ⟨⟨⟨1700966359,677121751⟩,⟨1717157459,1551021537⟩⟩,⟨⟨1850621594,1189514123⟩,⟨1824633388,1447799076⟩⟩⟩
def h2 : FE := ⟨⟨⟨1140574374,1707823330⟩,⟨2074018337,1150348803⟩⟩,⟨⟨901324147,375545467⟩,⟨460679338,2048710537⟩⟩⟩
def d3 : FE := ⟨⟨⟨1039367122,225930383⟩,⟨788194480,1728281297⟩⟩,⟨⟨1325536372,248707082⟩,⟨1886287452,19462060⟩⟩⟩
def h3 : FE := ⟨⟨⟨1115316625,1249583729⟩,⟨1980336543,1532493872⟩⟩,⟨⟨1413419984,825076880⟩,⟨2072152983,1184212769⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨1892306820,457026648⟩,⟨1244089518,1601574450⟩⟩,⟨⟨811122085,1218398195⟩,⟨100105464,1838486736⟩⟩⟩
def t1 : FE := ⟨⟨⟨1910907670,1597928687⟩,⟨2032287937,1721102572⟩⟩,⟨⟨696176349,218579058⟩,⟨949313786,1971742411⟩⟩⟩
def value : FE := ⟨⟨⟨1345579330,252607270⟩,⟨2100509967,628802256⟩⟩,⟨⟨245603780,1844768942⟩,⟨1576033504,1382024442⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 3).x)⁻¹=(305966207 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 741659990 305966207 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 3).y)⁻¹=(1686928114 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1452551567 1686928114 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1686928114)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*305966207)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*305966207*1686928114)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 305966207)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1686928114)
    (Port5Q1_OpeningValues.values JHa_Dots3.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 305966207=(305966207:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1686928114=(1686928114:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots3.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots3.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots3.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots3.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots3.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 3)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle3.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots3.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1345579330<2147483647 ∧ 252607270<2147483647) ∧ (2100509967<2147483647 ∧ 628802256<2147483647)) ∧
      ((245603780<2147483647 ∧ 1844768942<2147483647) ∧ (1576033504<2147483647 ∧ 1382024442<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle3
end
