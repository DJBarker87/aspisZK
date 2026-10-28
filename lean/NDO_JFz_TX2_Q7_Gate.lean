import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q7_Slot0
import NDO_JFz_TX2_Q7_Slot1
import NDO_JFz_TX2_Q7_Slot2
import NDO_JFz_TX2_Q7_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q7_Dot0.value,JFz_TX2_Q7_Dot1.value,JFz_TX2_Q7_Dot2.value,JFz_TX2_Q7_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 7=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q7_Dot0.source,JFz_TX2_Q7_Dot1.source,
    JFz_TX2_Q7_Dot2.source,JFz_TX2_Q7_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q7_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨2088360539,351922770⟩,⟨1515355897,576244497⟩⟩,⟨⟨1560730970,1284076736⟩,⟨101089849,1953631681⟩⟩⟩
def h1 : FE := ⟨⟨⟨572130197,372918615⟩,⟨624826143,1726854846⟩⟩,⟨⟨500528986,676149467⟩,⟨1228436315,839531705⟩⟩⟩
def h2 : FE := ⟨⟨⟨1813249436,2132235751⟩,⟨334127700,883702514⟩⟩,⟨⟨247449716,658560983⟩,⟨1666032142,1643719240⟩⟩⟩
def h3 : FE := ⟨⟨⟨1277080004,1877557149⟩,⟨181732675,1521217048⟩⟩,⟨⟨1555802352,686602918⟩,⟨1595566074,1317621876⟩⟩⟩
def t2 : FE := ⟨⟨⟨996809012,377134021⟩,⟨1918307177,995161049⟩⟩,⟨⟨1744097135,753026573⟩,⟨82988108,466673436⟩⟩⟩
def t1 : FE := ⟨⟨⟨525550748,1015167435⟩,⟨617567252,922479295⟩⟩,⟨⟨1524420508,1249729484⟩,⟨1127165846,592961057⟩⟩⟩
def value : FE := ⟨⟨⟨1164781923,5833544⟩,⟨705381050,2001139904⟩⟩,⟨⟨743439455,722225228⟩,⟨1231690184,1580115047⟩⟩⟩
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
end AspisR1.JFz_TX2_Q7_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q7_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q7_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q7_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q7_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q7_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1956537571,1198486366⟩,⟨2138212601,446241813⟩⟩,⟨⟨791629907,1884514005⟩,⟨486081008,1093305685⟩⟩⟩+⟨⟨⟨1318339720,424562866⟩,⟨138995116,940281559⟩⟩,⟨⟨1092774950,1210154845⟩,⟨1049172698,1087780718⟩⟩⟩+⟨⟨⟨264509505,491021319⟩,⟨1814736956,1572687174⟩⟩,⟨⟨1631454550,1117463565⟩,⟨342065434,2082184645⟩⟩⟩+⟨⟨⟨519088066,1441104176⟩,⟨1969478915,1493251089⟩⟩,⟨⟨579580826,924174529⟩,⟨674523903,1403772029⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*755154715)=h1 := by
  change ((⟨⟨⟨1956537571,1198486366⟩,⟨2138212601,446241813⟩⟩,⟨⟨791629907,1884514005⟩,⟨486081008,1093305685⟩⟩⟩-⟨⟨⟨1318339720,424562866⟩,⟨138995116,940281559⟩⟩,⟨⟨1092774950,1210154845⟩,⟨1049172698,1087780718⟩⟩⟩-⟨⟨⟨264509505,491021319⟩,⟨1814736956,1572687174⟩⟩,⟨⟨1631454550,1117463565⟩,⟨342065434,2082184645⟩⟩⟩+⟨⟨⟨519088066,1441104176⟩,⟨1969478915,1493251089⟩⟩,⟨⟨579580826,924174529⟩,⟨674523903,1403772029⟩⟩⟩)*(536870912*755154715) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*528021205)=h2 := by
  change ((⟨⟨⟨1956537571,1198486366⟩,⟨2138212601,446241813⟩⟩,⟨⟨791629907,1884514005⟩,⟨486081008,1093305685⟩⟩⟩+⟨⟨⟨1318339720,424562866⟩,⟨138995116,940281559⟩⟩,⟨⟨1092774950,1210154845⟩,⟨1049172698,1087780718⟩⟩⟩-⟨⟨⟨264509505,491021319⟩,⟨1814736956,1572687174⟩⟩,⟨⟨1631454550,1117463565⟩,⟨342065434,2082184645⟩⟩⟩-⟨⟨⟨519088066,1441104176⟩,⟨1969478915,1493251089⟩⟩,⟨⟨579580826,924174529⟩,⟨674523903,1403772029⟩⟩⟩)*(536870912*528021205) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*528021205*755154715)=h3 := by
  change ((⟨⟨⟨1956537571,1198486366⟩,⟨2138212601,446241813⟩⟩,⟨⟨791629907,1884514005⟩,⟨486081008,1093305685⟩⟩⟩-⟨⟨⟨1318339720,424562866⟩,⟨138995116,940281559⟩⟩,⟨⟨1092774950,1210154845⟩,⟨1049172698,1087780718⟩⟩⟩+⟨⟨⟨264509505,491021319⟩,⟨1814736956,1572687174⟩⟩,⟨⟨1631454550,1117463565⟩,⟨342065434,2082184645⟩⟩⟩-⟨⟨⟨519088066,1441104176⟩,⟨1969478915,1493251089⟩⟩,⟨⟨579580826,924174529⟩,⟨674523903,1403772029⟩⟩⟩)*(536870912*528021205*755154715) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q7_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q7_CircleNumbers JFz_TX2_Q7_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 528021205=(528021205:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 755154715=(755154715:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q7_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q7_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q7_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q7_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 528021205)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 755154715)
    (Port5Q1_OpeningValues.values JFz_TX2_Q7_Dots0.value)=JFz_TX2_Q7_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q7_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value17_0.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).x)⁻¹=(528021205 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 859053651 528021205 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).y)⁻¹=(755154715 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1433077919 755154715 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 7) 0#usize=ok selected := JFn_Values17.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 7)
    (JFv_TX2_CircleGeometry.inverse err seed 7)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 7
  rw [x,y,JFz_TX2_Q7_Dots0.source,JFz_TX2_Q7_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q7_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1164781923<2147483647 ∧ 5833544<2147483647) ∧ (705381050<2147483647 ∧ 2001139904<2147483647)) ∧
      ((743439455<2147483647 ∧ 722225228<2147483647) ∧ (1231690184<2147483647 ∧ 1580115047<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q7_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1164781923,5833544⟩,⟨705381050,2001139904⟩⟩,⟨⟨743439455,722225228⟩,⟨1231690184,1580115047⟩⟩⟩
def d1 : FE := ⟨⟨⟨710555852,619358772⟩,⟨1186302413,802073952⟩⟩,⟨⟨290987046,1527341074⟩,⟨1784871996,1760991604⟩⟩⟩
def d2 : FE := ⟨⟨⟨1557813380,800746288⟩,⟨2071554914,1709222532⟩⟩,⟨⟨1234604824,561330694⟩,⟨2127535449,785094645⟩⟩⟩
def d3 : FE := ⟨⟨⟨1223599952,274875407⟩,⟨1758516167,752173464⟩⟩,⟨⟨1589272341,1766558798⟩,⟨1356246270,263686108⟩⟩⟩
def c0 : FE := ⟨⟨⟨71936958,1827875815⟩,⟨1356022234,1745758391⟩⟩,⟨⟨1435892656,2070145682⟩,⟨1441964972,1467455884⟩⟩⟩
def c1 : FE := ⟨⟨⟨220529160,1555955863⟩,⟨773367500,1142771885⟩⟩,⟨⟨1242574236,1838222373⟩,⟨1141717729,1359107130⟩⟩⟩
def h0 : FE := ⟨⟨⟨627316865,2035816238⟩,⟨1430438636,1316152463⟩⟩,⟨⟨2038317740,70622125⟩,⟨1088215063,1097471851⟩⟩⟩
def h1 : FE := ⟨⟨⟨146233059,1691915839⟩,⟨1064694867,1444265138⟩⟩,⟨⟨1339233446,880442204⟩,⟨218099527,1413281507⟩⟩⟩
def h2 : FE := ⟨⟨⟨1161023120,1232448912⟩,⟨451686601,1421514027⟩⟩,⟨⟨419903599,1239364287⟩,⟨1509542088,483649338⟩⟩⟩
def h3 : FE := ⟨⟨⟨2140021471,1011821983⟩,⟨1858677286,1374436652⟩⟩,⟨⟨1901877734,899249749⟩,⟨484125000,482459821⟩⟩⟩
def t2 : FE := ⟨⟨⟨403796927,1366405401⟩,⟨82571752,333404166⟩⟩,⟨⟨872098484,1888419100⟩,⟨329964304,617564191⟩⟩⟩
def t1 : FE := ⟨⟨⟨2056603093,1246407260⟩,⟨1496841122,507229606⟩⟩,⟨⟨1699279617,320808050⟩,⟨650843425,922614538⟩⟩⟩
def answer : FE := ⟨⟨⟨430211371,1975021750⟩,⟨1197545831,711065176⟩⟩,⟨⟨1363605586,1822937909⟩,⟨897522593,325453880⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨430211371#u32,1975021750#u32⟩,⟨1197545831#u32,711065176#u32⟩⟩,⟨⟨1363605586#u32,1822937909#u32⟩,⟨897522593#u32,325453880#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*4461333)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*1110240368)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*80080486)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*80080486)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).lineX)⁻¹=(4461333:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 2006341782 4461333 (by norm_num)
theorem cast0 : algebraMap FP FE 4461333=(4461333:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).lineY)⁻¹=(1110240368:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1738820246 1110240368 (by norm_num)
theorem cast1 : algebraMap FP FE 1110240368=(1110240368:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).lineZ)⁻¹=(80080486:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 609446502 80080486 (by norm_num)
theorem cast2 : algebraMap FP FE 80080486=(80080486:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 7) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 7) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 7) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 7) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 4461333) (algebraMap FP FE 1110240368) (algebraMap FP FE 80080486)
    (Port5Q1_OpeningValues.values (JFn_Values.value 7))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 7)
      (JFv_TX2_CircleGeometry.inverse err seed 7)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 7 (JFv_TX2_CircleGeometry.inverse err seed 7)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 7 2,
    JFv_TX2_CircleGeometry.decoded err seed 7 3,
    JFv_TX2_CircleGeometry.decoded err seed 7 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 7).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((430211371<2147483647 ∧ 1975021750<2147483647) ∧ (1197545831<2147483647 ∧ 711065176<2147483647)) ∧
      ((1363605586<2147483647 ∧ 1822937909<2147483647) ∧ (897522593<2147483647 ∧ 325453880<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q7_Line
end
