import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots9
import NDO_JGw_Circle9
import NDO_JGw_Values9
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle9
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value09_1.value
def d0 : FE := ⟨⟨⟨2091433889,216499546⟩,⟨646543183,1305197620⟩⟩,⟨⟨358695045,867523287⟩,⟨657368636,1837953874⟩⟩⟩
def h0 : FE := ⟨⟨⟨350465858,1358620174⟩,⟨1424163489,372045715⟩⟩,⟨⟨1132193993,1808985757⟩,⟨41136089,1151501896⟩⟩⟩
def d1 : FE := ⟨⟨⟨1421245089,1000920033⟩,⟨1221588714,695708557⟩⟩,⟨⟨1110421133,422436494⟩,⟨1188534145,525893899⟩⟩⟩
def h1 : FE := ⟨⟨⟨283077451,2006880299⟩,⟨1765803053,2104996749⟩⟩,⟨⟨1851823946,1533016139⟩,⟨1070792653,325748002⟩⟩⟩
def d2 : FE := ⟨⟨⟨2072349020,1219848130⟩,⟨1719168583,928845083⟩⟩,⟨⟨142017361,1012092072⟩,⟨2049535405,1268482942⟩⟩⟩
def h2 : FE := ⟨⟨⟨480712329,1624642198⟩,⟨1805852410,1548495906⟩⟩,⟨⟨166117686,1112217382⟩,⟨1160963559,675841521⟩⟩⟩
def d3 : FE := ⟨⟨⟨111802728,849729340⟩,⟨2109353476,705915247⟩⟩,⟨⟨770158786,638923881⟩,⟨564073464,973676869⟩⟩⟩
def h3 : FE := ⟨⟨⟨418761242,1765292775⟩,⟨436717472,1553667865⟩⟩,⟨⟨451733743,1982632046⟩,⟨1170173784,2003629363⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨2131693778,651374768⟩,⟨1572016404,720356397⟩⟩,⟨⟨1069328656,1763500450⟩,⟨480065074,1872330517⟩⟩⟩
def t1 : FE := ⟨⟨⟨761642070,2084150550⟩,⟨336664263,1961468318⟩⟩,⟨⟨1777401477,498836829⟩,⟨1212962500,1665200027⟩⟩⟩
def value : FE := ⟨⟨⟨1504351165,389464337⟩,⟨1673641914,919002449⟩⟩,⟨⟨1955910997,794125224⟩,⟨328630422,135755893⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 9).x)⁻¹=(1828152250 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1968041874 1828152250 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 9).y)⁻¹=(611330035 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1497023214 611330035 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*611330035)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*1828152250)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*1828152250*611330035)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1828152250)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 611330035)
    (Port5Q1_OpeningValues.values JHa_Dots9.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1828152250=(1828152250:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 611330035=(611330035:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots9.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots9.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots9.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots9.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots9.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 9)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle9.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots9.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1504351165<2147483647 ∧ 389464337<2147483647) ∧ (1673641914<2147483647 ∧ 919002449<2147483647)) ∧
      ((1955910997<2147483647 ∧ 794125224<2147483647) ∧ (328630422<2147483647 ∧ 135755893<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle9
end
