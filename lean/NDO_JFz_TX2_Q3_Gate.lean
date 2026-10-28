import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q3_Slot0
import NDO_JFz_TX2_Q3_Slot1
import NDO_JFz_TX2_Q3_Slot2
import NDO_JFz_TX2_Q3_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q3_Dot0.value,JFz_TX2_Q3_Dot1.value,JFz_TX2_Q3_Dot2.value,JFz_TX2_Q3_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 3=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q3_Dot0.source,JFz_TX2_Q3_Dot1.source,
    JFz_TX2_Q3_Dot2.source,JFz_TX2_Q3_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q3_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨331710821,1292512236⟩,⟨221409308,1456639581⟩⟩,⟨⟨1057384701,1044533974⟩,⟨186685275,1331437011⟩⟩⟩
def h1 : FE := ⟨⟨⟨2014320379,1486874925⟩,⟨1962658938,160292975⟩⟩,⟨⟨448001028,250571711⟩,⟨1905050296,309592456⟩⟩⟩
def h2 : FE := ⟨⟨⟨1742267678,516913465⟩,⟨1851652058,241846151⟩⟩,⟨⟨1105776660,1607207361⟩,⟨434087235,47753424⟩⟩⟩
def h3 : FE := ⟨⟨⟨29056946,1957545360⟩,⟨652576060,1885483517⟩⟩,⟨⟨222508830,614251596⟩,⟨510028834,1788362215⟩⟩⟩
def t2 : FE := ⟨⟨⟨1454406294,664332944⟩,⟨1467400990,972859959⟩⟩,⟨⟨817337915,1556584123⟩,⟨2113676914,870902036⟩⟩⟩
def t1 : FE := ⟨⟨⟨1274148733,1788054287⟩,⟨610598306,345168690⟩⟩,⟨⟨307246331,799779685⟩,⟨1020443242,1216312141⟩⟩⟩
def value : FE := ⟨⟨⟨901329660,294142851⟩,⟨332212484,2141990079⟩⟩,⟨⟨1613711982,83705593⟩,⟨1349691811,2036132375⟩⟩⟩
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
end AspisR1.JFz_TX2_Q3_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q3_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q3_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q3_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q3_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q3_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨339262139,732628543⟩,⟨1005963240,722757112⟩⟩,⟨⟨1413599205,1775077425⟩,⟨1426778238,1978410783⟩⟩⟩+⟨⟨⟨1995883035,903208221⟩,⟨57562012,1427931575⟩⟩,⟨⟨653240513,535753348⟩,⟨1368764700,1157119489⟩⟩⟩+⟨⟨⟨1248460411,264642389⟩,⟨1798166254,734378101⟩⟩,⟨⟨1793215929,1147034388⟩,⟨741278219,1229782693⟩⟩⟩+⟨⟨⟨2038204993,1122086144⟩,⟨171429373,794007889⟩⟩,⟨⟨369483157,720270735⟩,⟨1504887237,960435079⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1121811647)=h1 := by
  change ((⟨⟨⟨339262139,732628543⟩,⟨1005963240,722757112⟩⟩,⟨⟨1413599205,1775077425⟩,⟨1426778238,1978410783⟩⟩⟩-⟨⟨⟨1995883035,903208221⟩,⟨57562012,1427931575⟩⟩,⟨⟨653240513,535753348⟩,⟨1368764700,1157119489⟩⟩⟩-⟨⟨⟨1248460411,264642389⟩,⟨1798166254,734378101⟩⟩,⟨⟨1793215929,1147034388⟩,⟨741278219,1229782693⟩⟩⟩+⟨⟨⟨2038204993,1122086144⟩,⟨171429373,794007889⟩⟩,⟨⟨369483157,720270735⟩,⟨1504887237,960435079⟩⟩⟩)*(536870912*1121811647) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*91151177)=h2 := by
  change ((⟨⟨⟨339262139,732628543⟩,⟨1005963240,722757112⟩⟩,⟨⟨1413599205,1775077425⟩,⟨1426778238,1978410783⟩⟩⟩+⟨⟨⟨1995883035,903208221⟩,⟨57562012,1427931575⟩⟩,⟨⟨653240513,535753348⟩,⟨1368764700,1157119489⟩⟩⟩-⟨⟨⟨1248460411,264642389⟩,⟨1798166254,734378101⟩⟩,⟨⟨1793215929,1147034388⟩,⟨741278219,1229782693⟩⟩⟩-⟨⟨⟨2038204993,1122086144⟩,⟨171429373,794007889⟩⟩,⟨⟨369483157,720270735⟩,⟨1504887237,960435079⟩⟩⟩)*(536870912*91151177) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*91151177*1121811647)=h3 := by
  change ((⟨⟨⟨339262139,732628543⟩,⟨1005963240,722757112⟩⟩,⟨⟨1413599205,1775077425⟩,⟨1426778238,1978410783⟩⟩⟩-⟨⟨⟨1995883035,903208221⟩,⟨57562012,1427931575⟩⟩,⟨⟨653240513,535753348⟩,⟨1368764700,1157119489⟩⟩⟩+⟨⟨⟨1248460411,264642389⟩,⟨1798166254,734378101⟩⟩,⟨⟨1793215929,1147034388⟩,⟨741278219,1229782693⟩⟩⟩-⟨⟨⟨2038204993,1122086144⟩,⟨171429373,794007889⟩⟩,⟨⟨369483157,720270735⟩,⟨1504887237,960435079⟩⟩⟩)*(536870912*91151177*1121811647) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q3_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q3_CircleNumbers JFz_TX2_Q3_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 91151177=(91151177:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1121811647=(1121811647:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q3_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q3_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q3_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q3_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 91151177)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1121811647)
    (Port5Q1_OpeningValues.values JFz_TX2_Q3_Dots0.value)=JFz_TX2_Q3_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q3_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value13_0.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).x)⁻¹=(91151177 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 171471092 91151177 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).y)⁻¹=(1121811647 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 272206234 1121811647 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 3) 0#usize=ok selected := JFn_Values13.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 3)
    (JFv_TX2_CircleGeometry.inverse err seed 3)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 3
  rw [x,y,JFz_TX2_Q3_Dots0.source,JFz_TX2_Q3_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q3_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((901329660<2147483647 ∧ 294142851<2147483647) ∧ (332212484<2147483647 ∧ 2141990079<2147483647)) ∧
      ((1613711982<2147483647 ∧ 83705593<2147483647) ∧ (1349691811<2147483647 ∧ 2036132375<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q3_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨901329660,294142851⟩,⟨332212484,2141990079⟩⟩,⟨⟨1613711982,83705593⟩,⟨1349691811,2036132375⟩⟩⟩
def d1 : FE := ⟨⟨⟨596446522,1330378105⟩,⟨596315588,1904450947⟩⟩,⟨⟨1031734086,1814216634⟩,⟨842336361,353269271⟩⟩⟩
def d2 : FE := ⟨⟨⟨798909464,1890337013⟩,⟨1557033258,10729764⟩⟩,⟨⟨337453330,92243573⟩,⟨1926620657,2131245360⟩⟩⟩
def d3 : FE := ⟨⟨⟨1801361440,957058822⟩,⟨735934588,150456116⟩⟩,⟨⟨600325266,1525834106⟩,⟨165589068,1947284288⟩⟩⟩
def c0 : FE := ⟨⟨⟨847288719,1884906089⟩,⟨761178927,2083411947⟩⟩,⟨⟨409207407,1586912988⟩,⟨348160298,1557101982⟩⟩⟩
def c1 : FE := ⟨⟨⟨229232314,16310735⟩,⟨1289507074,698826334⟩⟩,⟨⟨736685570,849886236⟩,⟨575502375,1392758174⟩⟩⟩
def h0 : FE := ⟨⟨⟨2098253595,581108286⟩,⟨1879115803,2125648550⟩⟩,⟨⟨895806166,1952741800⟩,⟨1607930386,543241000⟩⟩⟩
def h1 : FE := ⟨⟨⟨1612002340,950608412⟩,⟨2099084824,317377317⟩⟩,⟨⟨1646688312,1218399612⟩,⟨1535573160,1474930078⟩⟩⟩
def h2 : FE := ⟨⟨⟨1814363789,1823949826⟩,⟨32783753,741030778⟩⟩,⟨⟨1370121694,2087410340⟩,⟨1475705663,523153643⟩⟩⟩
def h3 : FE := ⟨⟨⟨1368039996,1370508575⟩,⟨781678128,1154949739⟩⟩,⟨⟨1423672327,1911477512⟩,⟨341814412,19229872⟩⟩⟩
def t2 : FE := ⟨⟨⟨440636497,151285256⟩,⟨231317278,766956318⟩⟩,⟨⟨103148959,1425076227⟩,⟨2142223936,734004589⟩⟩⟩
def t1 : FE := ⟨⟨⟨1100278756,173678559⟩,⟨1263267064,1767076413⟩⟩,⟨⟨598212875,531403224⟩,⟨658131218,1318922619⟩⟩⟩
def answer : FE := ⟨⟨⟨1196992877,1181068234⟩,⟨1545351490,821525277⟩⟩,⟨⟨1465320702,866790779⟩,⟨354632043,1561293945⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨1196992877#u32,1181068234#u32⟩,⟨1545351490#u32,821525277#u32⟩⟩,⟨⟨1465320702#u32,866790779#u32⟩,⟨354632043#u32,1561293945#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*1172889265)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*1318829154)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1230353286)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1230353286)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).lineX)⁻¹=(1172889265:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1523492401 1172889265 (by norm_num)
theorem cast0 : algebraMap FP FE 1172889265=(1172889265:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).lineY)⁻¹=(1318829154:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 2079565300 1318829154 (by norm_num)
theorem cast1 : algebraMap FP FE 1318829154=(1318829154:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).lineZ)⁻¹=(1230353286:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 777451883 1230353286 (by norm_num)
theorem cast2 : algebraMap FP FE 1230353286=(1230353286:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 3) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 3) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 3) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 3) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 1172889265) (algebraMap FP FE 1318829154) (algebraMap FP FE 1230353286)
    (Port5Q1_OpeningValues.values (JFn_Values.value 3))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 3)
      (JFv_TX2_CircleGeometry.inverse err seed 3)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 3 (JFv_TX2_CircleGeometry.inverse err seed 3)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 3 2,
    JFv_TX2_CircleGeometry.decoded err seed 3 3,
    JFv_TX2_CircleGeometry.decoded err seed 3 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 3).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((1196992877<2147483647 ∧ 1181068234<2147483647) ∧ (1545351490<2147483647 ∧ 821525277<2147483647)) ∧
      ((1465320702<2147483647 ∧ 866790779<2147483647) ∧ (354632043<2147483647 ∧ 1561293945<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q3_Line
end
