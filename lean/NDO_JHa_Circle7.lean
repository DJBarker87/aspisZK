import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots7
import NDO_JGw_Circle7
import NDO_JGw_Values7
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle7
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value07_3.value
def d0 : FE := ⟨⟨⟨962069884,839972696⟩,⟨1725131276,950599079⟩⟩,⟨⟨632946433,390238319⟩,⟨962312768,1697566241⟩⟩⟩
def h0 : FE := ⟨⟨⟨289936928,1852878665⟩,⟨2069369459,702440287⟩⟩,⟨⟨2138534807,1143571801⟩,⟨2057877229,1903072501⟩⟩⟩
def d1 : FE := ⟨⟨⟨1534474703,67909717⟩,⟨962453307,1413958541⟩⟩,⟨⟨2053497442,867535881⟩,⟨991576841,344156755⟩⟩⟩
def h1 : FE := ⟨⟨⟨1288565280,508262569⟩,⟨1101322312,370521291⟩⟩,⟨⟨406052237,78825751⟩,⟨246529678,1490385327⟩⟩⟩
def d2 : FE := ⟨⟨⟨139475372,1489885560⟩,⟨604296250,1246975836⟩⟩,⟨⟨608204704,772800491⟩,⟨1987217491,756272758⟩⟩⟩
def h2 : FE := ⟨⟨⟨1426406713,1664108849⟩,⟨1403678347,687862265⟩⟩,⟨⟨1833182944,1189336156⟩,⟨269972624,434796460⟩⟩⟩
def d3 : FE := ⟨⟨⟨671211400,718779393⟩,⟨690629709,1345711339⟩⟩,⟨⟨964523355,396228866⟩,⟨2142918169,519326956⟩⟩⟩
def h3 : FE := ⟨⟨⟨773824884,1904616788⟩,⟨1122702891,1653892885⟩⟩,⟨⟨1224868389,143771869⟩,⟨1254963483,1578771370⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨1508314965,181379751⟩,⟨736788319,1784781175⟩⟩,⟨⟨842340885,914232337⟩,⟨311703897,983493651⟩⟩⟩
def t1 : FE := ⟨⟨⟨1969518494,1670429582⟩,⟨794623330,357685372⟩⟩,⟨⟨1986322098,745336525⟩,⟨1922485083,1800235⟩⟩⟩
def value : FE := ⟨⟨⟨1624881175,334229555⟩,⟨1231804413,2095236360⟩⟩,⟨⟨394298181,127601937⟩,⟨180333677,1814595571⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 7).x)⁻¹=(8944873 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1389102654 8944873 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 7).y)⁻¹=(1886316611 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 473465904 1886316611 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1886316611)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*8944873)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*8944873*1886316611)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 8944873)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1886316611)
    (Port5Q1_OpeningValues.values JHa_Dots7.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 8944873=(8944873:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1886316611=(1886316611:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots7.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots7.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots7.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots7.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots7.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 7)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle7.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots7.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1624881175<2147483647 ∧ 334229555<2147483647) ∧ (1231804413<2147483647 ∧ 2095236360<2147483647)) ∧
      ((394298181<2147483647 ∧ 127601937<2147483647) ∧ (180333677<2147483647 ∧ 1814595571<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle7
end
