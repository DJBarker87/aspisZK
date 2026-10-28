import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots2
import NDO_JGw_Circle2
import NDO_JGw_Values2
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle2
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value02_3.value
def d0 : FE := ⟨⟨⟨96581048,1544788512⟩,⟨2015746449,292679947⟩⟩,⟨⟨177113647,666820863⟩,⟨1428735792,2082279749⟩⟩⟩
def h0 : FE := ⟨⟨⟨1661872079,119899857⟩,⟨636481344,981750319⟩⟩,⟨⟨108336866,1366225892⟩,⟨2096806101,745753101⟩⟩⟩
def d1 : FE := ⟨⟨⟨1227710331,1387729318⟩,⟨1827069504,845580921⟩⟩,⟨⟨524622376,1286669910⟩,⟨1485867935,550658571⟩⟩⟩
def h1 : FE := ⟨⟨⟨1399269962,1065868727⟩,⟨1148794131,852689107⟩⟩,⟨⟨1893035495,1359667804⟩,⟨1538754324,1959606484⟩⟩⟩
def d2 : FE := ⟨⟨⟨1612640045,83763139⟩,⟨1492546388,1326071024⟩⟩,⟨⟨693208606,1306601584⟩,⟨990664624,1795172001⟩⟩⟩
def h2 : FE := ⟨⟨⟨1642349168,1064058143⟩,⟨205808597,843681244⟩⟩,⟨⟨1469290505,1754423567⟩,⟨625218186,219208893⟩⟩⟩
def d3 : FE := ⟨⟨⟨1563073245,1758285753⟩,⟨1505530329,1462669384⟩⟩,⟨⟨1185886482,57327564⟩,⟨186988759,702385730⟩⟩⟩
def h3 : FE := ⟨⟨⟨92898502,1910653827⟩,⟨218791559,1387800253⟩⟩,⟨⟨1135066786,925014285⟩,⟨1126652967,1938498434⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨1217600766,1255879774⟩,⟨1550691126,413225955⟩⟩,⟨⟨365187369,2059417896⟩,⟨1429046671,806942416⟩⟩⟩
def t1 : FE := ⟨⟨⟨1011095006,206471733⟩,⟨600108982,1631895266⟩⟩,⟨⟨1209680935,1558761⟩,⟨736804504,90122988⟩⟩⟩
def value : FE := ⟨⟨⟨2105904998,1610425956⟩,⟨641719873,1829180105⟩⟩,⟨⟨146852901,1495337783⟩,⟨1441999667,1898936014⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 2).x)⁻¹=(150461799 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 2071054496 150461799 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 2).y)⁻¹=(1244896936 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1264348651 1244896936 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1244896936)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*150461799)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*150461799*1244896936)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 150461799)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1244896936)
    (Port5Q1_OpeningValues.values JHa_Dots2.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 150461799=(150461799:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1244896936=(1244896936:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots2.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots2.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots2.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots2.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots2.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 2)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle2.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots2.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((2105904998<2147483647 ∧ 1610425956<2147483647) ∧ (641719873<2147483647 ∧ 1829180105<2147483647)) ∧
      ((146852901<2147483647 ∧ 1495337783<2147483647) ∧ (1441999667<2147483647 ∧ 1898936014<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle2
end
