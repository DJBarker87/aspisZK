import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q4_Slot0
import NDO_JFz_TX2_Q4_Slot1
import NDO_JFz_TX2_Q4_Slot2
import NDO_JFz_TX2_Q4_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q4_Dot0.value,JFz_TX2_Q4_Dot1.value,JFz_TX2_Q4_Dot2.value,JFz_TX2_Q4_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 4=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q4_Dot0.source,JFz_TX2_Q4_Dot1.source,
    JFz_TX2_Q4_Dot2.source,JFz_TX2_Q4_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q4_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨345496773,1049924703⟩,⟨113860959,1220362947⟩⟩,⟨⟨761678351,54592924⟩,⟨770712198,82732005⟩⟩⟩
def h1 : FE := ⟨⟨⟨222074288,280946001⟩,⟨461817484,1315630758⟩⟩,⟨⟨1104256763,344708852⟩,⟨903955456,1738382254⟩⟩⟩
def h2 : FE := ⟨⟨⟨1301551486,656352407⟩,⟨1098963730,260949973⟩⟩,⟨⟨102109263,234509282⟩,⟨429145203,1448847370⟩⟩⟩
def h3 : FE := ⟨⟨⟨408232744,1799907674⟩,⟨1827807297,1583832368⟩⟩,⟨⟨1960643235,451396890⟩,⟨1888035543,1257658562⟩⟩⟩
def t2 : FE := ⟨⟨⟨1473168861,863357006⟩,⟨448385026,278146727⟩⟩,⟨⟨1509384275,845919175⟩,⟨684698776,2089348693⟩⟩⟩
def t1 : FE := ⟨⟨⟨889816524,83478871⟩,⟨923971227,2108775113⟩⟩,⟨⟨462161036,1250859597⟩,⟨253848787,1893279413⟩⟩⟩
def value : FE := ⟨⟨⟨1424593160,1293249796⟩,⟨348390295,1333414861⟩⟩,⟨⟨749271607,1040919152⟩,⟨1068818580,2102458512⟩⟩⟩
theorem quarter : (4:FE)⁻¹=536870912 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem horner2 : h2+alpha*h3=t2 := by
  unfold h2 alpha h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem horner1 : h1+alpha*t2=t1 := by
  unfold h1 alpha t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem horner0 : h0+alpha*t1=value := by
  unfold h0 alpha t1 value
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms quarter
#print axioms horner2
#print axioms horner1
#print axioms horner0
end AspisR1.JFz_TX2_Q4_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q4_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q4_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q4_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q4_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q4_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1606296961,2103778778⟩,⟨901120435,1891056613⟩⟩,⟨⟨932407918,1922210071⟩,⟨485445813,2059286268⟩⟩⟩+⟨⟨⟨114919171,1430559108⟩,⟨562490156,1501816500⟩⟩,⟨⟨565542367,300445846⟩,⟨1895202562,241999749⟩⟩⟩+⟨⟨⟨238758231,882853788⟩,⟨2053244893,491698102⟩⟩,⟨⟨1244921173,1360988233⟩,⟨104551013,1582541846⟩⟩⟩+⟨⟨⟨1569496376,1929990785⟩,⟨1233555646,996880573⟩⟩,⟨⟨303841946,929694840⟩,⟨597649404,742067451⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*835007212)=h1 := by
  change ((⟨⟨⟨1606296961,2103778778⟩,⟨901120435,1891056613⟩⟩,⟨⟨932407918,1922210071⟩,⟨485445813,2059286268⟩⟩⟩-⟨⟨⟨114919171,1430559108⟩,⟨562490156,1501816500⟩⟩,⟨⟨565542367,300445846⟩,⟨1895202562,241999749⟩⟩⟩-⟨⟨⟨238758231,882853788⟩,⟨2053244893,491698102⟩⟩,⟨⟨1244921173,1360988233⟩,⟨104551013,1582541846⟩⟩⟩+⟨⟨⟨1569496376,1929990785⟩,⟨1233555646,996880573⟩⟩,⟨⟨303841946,929694840⟩,⟨597649404,742067451⟩⟩⟩)*(536870912*835007212) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*1598434689)=h2 := by
  change ((⟨⟨⟨1606296961,2103778778⟩,⟨901120435,1891056613⟩⟩,⟨⟨932407918,1922210071⟩,⟨485445813,2059286268⟩⟩⟩+⟨⟨⟨114919171,1430559108⟩,⟨562490156,1501816500⟩⟩,⟨⟨565542367,300445846⟩,⟨1895202562,241999749⟩⟩⟩-⟨⟨⟨238758231,882853788⟩,⟨2053244893,491698102⟩⟩,⟨⟨1244921173,1360988233⟩,⟨104551013,1582541846⟩⟩⟩-⟨⟨⟨1569496376,1929990785⟩,⟨1233555646,996880573⟩⟩,⟨⟨303841946,929694840⟩,⟨597649404,742067451⟩⟩⟩)*(536870912*1598434689) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*1598434689*835007212)=h3 := by
  change ((⟨⟨⟨1606296961,2103778778⟩,⟨901120435,1891056613⟩⟩,⟨⟨932407918,1922210071⟩,⟨485445813,2059286268⟩⟩⟩-⟨⟨⟨114919171,1430559108⟩,⟨562490156,1501816500⟩⟩,⟨⟨565542367,300445846⟩,⟨1895202562,241999749⟩⟩⟩+⟨⟨⟨238758231,882853788⟩,⟨2053244893,491698102⟩⟩,⟨⟨1244921173,1360988233⟩,⟨104551013,1582541846⟩⟩⟩-⟨⟨⟨1569496376,1929990785⟩,⟨1233555646,996880573⟩⟩,⟨⟨303841946,929694840⟩,⟨597649404,742067451⟩⟩⟩)*(536870912*1598434689*835007212) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q4_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q4_CircleNumbers JFz_TX2_Q4_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1598434689=(1598434689:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 835007212=(835007212:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q4_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q4_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q4_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q4_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1598434689)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 835007212)
    (Port5Q1_OpeningValues.values JFz_TX2_Q4_Dots0.value)=JFz_TX2_Q4_CircleNumbers.value := by
  rw [scalar,ix,iy]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms scalar
#print axioms ix
#print axioms iy
#print axioms v0
#print axioms v1
#print axioms v2
#print axioms v3
#print axioms formula
end AspisR1.JFz_TX2_Q4_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value14_1.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).x)⁻¹=(1598434689 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1485660594 1598434689 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).y)⁻¹=(835007212 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 424270521 835007212 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 4) 1#usize=ok selected := JFn_Values14.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 4)
    (JFv_TX2_CircleGeometry.inverse err seed 4)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 4
  rw [x,y,JFz_TX2_Q4_Dots0.source,JFz_TX2_Q4_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q4_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1424593160<2147483647 ∧ 1293249796<2147483647) ∧ (348390295<2147483647 ∧ 1333414861<2147483647)) ∧
      ((749271607<2147483647 ∧ 1040919152<2147483647) ∧ (1068818580<2147483647 ∧ 2102458512<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q4_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨273788683,1773826581⟩,⟨260407785,791315104⟩⟩,⟨⟨1317719530,1055406027⟩,⟨801805620,1906357217⟩⟩⟩
def d1 : FE := ⟨⟨⟨1424593160,1293249796⟩,⟨348390295,1333414861⟩⟩,⟨⟨749271607,1040919152⟩,⟨1068818580,2102458512⟩⟩⟩
def d2 : FE := ⟨⟨⟨1725591817,1600368105⟩,⟨1962128425,1423876966⟩⟩,⟨⟨1892905843,254724859⟩,⟨1294731904,88775738⟩⟩⟩
def d3 : FE := ⟨⟨⟨135209354,168254927⟩,⟨1172642875,449892866⟩⟩,⟨⟨1545500196,1578417873⟩,⟨1609871249,1739085228⟩⟩⟩
def c0 : FE := ⟨⟨⟨2066087483,1101243230⟩,⟨813162474,1087540564⟩⟩,⟨⟨326322056,430165334⟩,⟨780912893,823276049⟩⟩⟩
def c1 : FE := ⟨⟨⟨1463213903,1987425376⟩,⟨1752571169,459535782⟩⟩,⟨⟨1937967987,309941258⟩,⟨328312228,878729538⟩⟩⟩
def h0 : FE := ⟨⟨⟨1963537577,1745795764⟩,⟨935892345,1536495861⟩⟩,⟨⟨1376349294,445496066⟩,⟨1730677750,922298262⟩⟩⟩
def h1 : FE := ⟨⟨⟨1764650693,1544334303⟩,⟨209124998,773538173⟩⟩,⟨⟨58403198,370053296⟩,⟨1628354384,1924744617⟩⟩⟩
def h2 : FE := ⟨⟨⟨1837319779,1472820726⟩,⟨75940855,1322059336⟩⟩,⟨⟨72934390,1247943326⟩,⟨221319154,1232691560⟩⟩⟩
def h3 : FE := ⟨⟨⟨1344842026,1175801246⟩,⟨1224966000,520014402⟩⟩,⟨⟨878487000,171344368⟩,⟨1296747359,662027447⟩⟩⟩
def t2 : FE := ⟨⟨⟨1803412928,2024161204⟩,⟨1312847308,1975402646⟩⟩,⟨⟨16318606,1298636594⟩,⟨1762573885,1004189573⟩⟩⟩
def t1 : FE := ⟨⟨⟨907012166,2131094441⟩,⟨125269068,1550251785⟩⟩,⟨⟨1928046263,1753829930⟩,⟨1443506190,304544662⟩⟩⟩
def answer : FE := ⟨⟨⟨2019700776,333543342⟩,⟨1284968521,19432796⟩⟩,⟨⟨2050529981,1578683472⟩,⟨352463402,1667445702⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨2019700776#u32,333543342#u32⟩,⟨1284968521#u32,19432796#u32⟩⟩,⟨⟨2050529981#u32,1578683472#u32⟩,⟨352463402#u32,1667445702#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*468091051)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*838001952)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1675562056)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1675562056)=h3 := by
  unfold c0 c1 h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h3_eq
theorem horner2 : h2+alpha*h3=t2 := by
  unfold h2 alpha h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner2
theorem horner1 : h1+alpha*t2=t1 := by
  unfold h1 alpha t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner1
theorem horner0 : h0+alpha*t1=answer := by
  unfold h0 alpha t1 answer
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner0
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).lineX)⁻¹=(468091051:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1052851067 468091051 (by norm_num)
theorem cast0 : algebraMap FP FE 468091051=(468091051:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).lineY)⁻¹=(838001952:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1698415954 838001952 (by norm_num)
theorem cast1 : algebraMap FP FE 838001952=(838001952:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).lineZ)⁻¹=(1675562056:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1612219610 1675562056 (by norm_num)
theorem cast2 : algebraMap FP FE 1675562056=(1675562056:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 4) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 4) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 4) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 4) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 468091051) (algebraMap FP FE 838001952) (algebraMap FP FE 1675562056)
    (Port5Q1_OpeningValues.values (JFn_Values.value 4))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 4)
      (JFv_TX2_CircleGeometry.inverse err seed 4)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 4 (JFv_TX2_CircleGeometry.inverse err seed 4)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 4 2,
    JFv_TX2_CircleGeometry.decoded err seed 4 3,
    JFv_TX2_CircleGeometry.decoded err seed 4 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 4).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((2019700776<2147483647 ∧ 333543342<2147483647) ∧ (1284968521<2147483647 ∧ 19432796<2147483647)) ∧
      ((2050529981<2147483647 ∧ 1578683472<2147483647) ∧ (352463402<2147483647 ∧ 1667445702<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q4_Line
end
