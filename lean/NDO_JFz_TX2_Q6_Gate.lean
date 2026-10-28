import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q6_Slot0
import NDO_JFz_TX2_Q6_Slot1
import NDO_JFz_TX2_Q6_Slot2
import NDO_JFz_TX2_Q6_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q6_Dot0.value,JFz_TX2_Q6_Dot1.value,JFz_TX2_Q6_Dot2.value,JFz_TX2_Q6_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 6=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q6_Dot0.source,JFz_TX2_Q6_Dot1.source,
    JFz_TX2_Q6_Dot2.source,JFz_TX2_Q6_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q6_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨1948324115,1770243747⟩,⟨1748369765,102134923⟩⟩,⟨⟨883950513,862238932⟩,⟨1662778942,1833751237⟩⟩⟩
def h1 : FE := ⟨⟨⟨1975117865,1909993337⟩,⟨1236364220,586658408⟩⟩,⟨⟨1977381219,1464931685⟩,⟨1136299859,929869964⟩⟩⟩
def h2 : FE := ⟨⟨⟨1279505484,2022251307⟩,⟨1461627551,1439439804⟩⟩,⟨⟨1890313895,387945390⟩,⟨1842719542,292558618⟩⟩⟩
def h3 : FE := ⟨⟨⟨1006215411,1633975957⟩,⟨1138743316,104932083⟩⟩,⟨⟨1615496977,1499157792⟩,⟨1773462047,617712077⟩⟩⟩
def t2 : FE := ⟨⟨⟨1903790245,266421534⟩,⟨1059087944,1383412951⟩⟩,⟨⟨1377064251,73160228⟩,⟨1241728879,1636633963⟩⟩⟩
def t1 : FE := ⟨⟨⟨1615383892,1333303089⟩,⟨1768538380,2001861745⟩⟩,⟨⟨1967060051,137179479⟩,⟨1573758549,840818859⟩⟩⟩
def value : FE := ⟨⟨⟨433885726,799164942⟩,⟨1270989458,211268664⟩⟩,⟨⟨438802342,1380386303⟩,⟨900251607,290924911⟩⟩⟩
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
end AspisR1.JFz_TX2_Q6_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q6_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q6_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q6_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q6_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q6_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1829480575,1628165367⟩,⟨584601343,340442191⟩⟩,⟨⟨848751639,1997421288⟩,⟨696770404,1348181983⟩⟩⟩+⟨⟨⟨1125795589,478613190⟩,⟨555046071,1233350556⟩⟩,⟨⟨359933609,1219205519⟩,⟨1577721399,1091247750⟩⟩⟩+⟨⟨⟨756213057,1257445277⟩,⟨1835100065,66311472⟩⟩,⟨⟨724582173,368171061⟩,⟨1997062768,1570129745⟩⟩⟩+⟨⟨⟨1934323592,1569267507⟩,⟨1871247934,915919120⟩⟩,⟨⟨1602534631,2011641507⟩,⟨232077550,1177961823⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1453114288)=h1 := by
  change ((⟨⟨⟨1829480575,1628165367⟩,⟨584601343,340442191⟩⟩,⟨⟨848751639,1997421288⟩,⟨696770404,1348181983⟩⟩⟩-⟨⟨⟨1125795589,478613190⟩,⟨555046071,1233350556⟩⟩,⟨⟨359933609,1219205519⟩,⟨1577721399,1091247750⟩⟩⟩-⟨⟨⟨756213057,1257445277⟩,⟨1835100065,66311472⟩⟩,⟨⟨724582173,368171061⟩,⟨1997062768,1570129745⟩⟩⟩+⟨⟨⟨1934323592,1569267507⟩,⟨1871247934,915919120⟩⟩,⟨⟨1602534631,2011641507⟩,⟨232077550,1177961823⟩⟩⟩)*(536870912*1453114288) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*7976418)=h2 := by
  change ((⟨⟨⟨1829480575,1628165367⟩,⟨584601343,340442191⟩⟩,⟨⟨848751639,1997421288⟩,⟨696770404,1348181983⟩⟩⟩+⟨⟨⟨1125795589,478613190⟩,⟨555046071,1233350556⟩⟩,⟨⟨359933609,1219205519⟩,⟨1577721399,1091247750⟩⟩⟩-⟨⟨⟨756213057,1257445277⟩,⟨1835100065,66311472⟩⟩,⟨⟨724582173,368171061⟩,⟨1997062768,1570129745⟩⟩⟩-⟨⟨⟨1934323592,1569267507⟩,⟨1871247934,915919120⟩⟩,⟨⟨1602534631,2011641507⟩,⟨232077550,1177961823⟩⟩⟩)*(536870912*7976418) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*7976418*1453114288)=h3 := by
  change ((⟨⟨⟨1829480575,1628165367⟩,⟨584601343,340442191⟩⟩,⟨⟨848751639,1997421288⟩,⟨696770404,1348181983⟩⟩⟩-⟨⟨⟨1125795589,478613190⟩,⟨555046071,1233350556⟩⟩,⟨⟨359933609,1219205519⟩,⟨1577721399,1091247750⟩⟩⟩+⟨⟨⟨756213057,1257445277⟩,⟨1835100065,66311472⟩⟩,⟨⟨724582173,368171061⟩,⟨1997062768,1570129745⟩⟩⟩-⟨⟨⟨1934323592,1569267507⟩,⟨1871247934,915919120⟩⟩,⟨⟨1602534631,2011641507⟩,⟨232077550,1177961823⟩⟩⟩)*(536870912*7976418*1453114288) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q6_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q6_CircleNumbers JFz_TX2_Q6_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 7976418=(7976418:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1453114288=(1453114288:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q6_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q6_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q6_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q6_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 7976418)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1453114288)
    (Port5Q1_OpeningValues.values JFz_TX2_Q6_Dots0.value)=JFz_TX2_Q6_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q6_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value16_2.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).x)⁻¹=(7976418 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1042108484 7976418 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).y)⁻¹=(1453114288 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1331627924 1453114288 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 6) 2#usize=ok selected := JFn_Values16.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 6)
    (JFv_TX2_CircleGeometry.inverse err seed 6)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 6
  rw [x,y,JFz_TX2_Q6_Dots0.source,JFz_TX2_Q6_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q6_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((433885726<2147483647 ∧ 799164942<2147483647) ∧ (1270989458<2147483647 ∧ 211268664<2147483647)) ∧
      ((438802342<2147483647 ∧ 1380386303<2147483647) ∧ (900251607<2147483647 ∧ 290924911<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q6_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1645515821,1240656743⟩,⟨654046506,879080589⟩⟩,⟨⟨1716804485,761274092⟩,⟨522936145,1747388490⟩⟩⟩
def d1 : FE := ⟨⟨⟨761665955,1216452524⟩,⟨1641480485,657124396⟩⟩,⟨⟨1654126825,1271579678⟩,⟨1636670801,1414412887⟩⟩⟩
def d2 : FE := ⟨⟨⟨433885726,799164942⟩,⟨1270989458,211268664⟩⟩,⟨⟨438802342,1380386303⟩,⟨900251607,290924911⟩⟩⟩
def d3 : FE := ⟨⟨⟨824109249,1055461204⟩,⟨498236731,726239408⟩⟩,⟨⟨864580662,722374172⟩,⟨1169491654,676743912⟩⟩⟩
def c0 : FE := ⟨⟨⟨2035660958,1321177398⟩,⟨1637201372,1955398398⟩⟩,⟨⟨1571644649,1069626626⟩,⟨140469115,1036036096⟩⟩⟩
def c1 : FE := ⟨⟨⟨22123889,1137665095⟩,⟨2083459126,1757567042⟩⟩,⟨⟨1382576386,1659408865⟩,⟨1881651721,374080137⟩⟩⟩
def h0 : FE := ⟨⟨⟨379423276,1614804765⟩,⟨1016188295,1155299176⟩⟩,⟨⟨94836755,1570774473⟩,⟨520466640,1032367550⟩⟩⟩
def h1 : FE := ⟨⟨⟨2102634247,155679423⟩,⟨1860330249,1856482720⟩⟩,⟨⟨403368694,290775922⟩,⟨1011060418,1778799940⟩⟩⟩
def h2 : FE := ⟨⟨⟨509061803,1722167347⟩,⟨1874431049,1923935016⟩⟩,⟨⟨489543415,460820878⟩,⟨1662433786,982214265⟩⟩⟩
def h3 : FE := ⟨⟨⟨1439750619,2103890352⟩,⟨1686625221,105770286⟩⟩,⟨⟨1378504553,554790322⟩,⟨901668079,1757515049⟩⟩⟩
def t2 : FE := ⟨⟨⟨287765215,1467322046⟩,⟨613225083,1591114605⟩⟩,⟨⟨1991159570,405265907⟩,⟨208789539,993684572⟩⟩⟩
def t1 : FE := ⟨⟨⟨1438114209,1618240745⟩,⟨1434593089,16517860⟩⟩,⟨⟨234277355,122757743⟩,⟨946991373,1880686065⟩⟩⟩
def answer : FE := ⟨⟨⟨1631962018,1945621887⟩,⟨1848361085,1407575532⟩⟩,⟨⟨901441731,244250042⟩,⟨1894152443,891495770⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨1631962018#u32,1945621887#u32⟩,⟨1848361085#u32,1407575532#u32⟩⟩,⟨⟨901441731#u32,244250042#u32⟩,⟨1894152443#u32,891495770#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*442415534)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*99352581)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*951390545)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*951390545)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).lineX)⁻¹=(442415534:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1010241389 442415534 (by norm_num)
theorem cast0 : algebraMap FP FE 442415534=(442415534:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).lineY)⁻¹=(99352581:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1385300719 99352581 (by norm_num)
theorem cast1 : algebraMap FP FE 99352581=(99352581:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).lineZ)⁻¹=(951390545:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 741299484 951390545 (by norm_num)
theorem cast2 : algebraMap FP FE 951390545=(951390545:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 6) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 6) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 6) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 6) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 442415534) (algebraMap FP FE 99352581) (algebraMap FP FE 951390545)
    (Port5Q1_OpeningValues.values (JFn_Values.value 6))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 6)
      (JFv_TX2_CircleGeometry.inverse err seed 6)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 6 (JFv_TX2_CircleGeometry.inverse err seed 6)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 6 2,
    JFv_TX2_CircleGeometry.decoded err seed 6 3,
    JFv_TX2_CircleGeometry.decoded err seed 6 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 6).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((1631962018<2147483647 ∧ 1945621887<2147483647) ∧ (1848361085<2147483647 ∧ 1407575532<2147483647)) ∧
      ((901441731<2147483647 ∧ 244250042<2147483647) ∧ (1894152443<2147483647 ∧ 891495770<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q6_Line
end
