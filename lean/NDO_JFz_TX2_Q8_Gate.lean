import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q8_Slot0
import NDO_JFz_TX2_Q8_Slot1
import NDO_JFz_TX2_Q8_Slot2
import NDO_JFz_TX2_Q8_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q8_Dot0.value,JFz_TX2_Q8_Dot1.value,JFz_TX2_Q8_Dot2.value,JFz_TX2_Q8_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 8=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q8_Dot0.source,JFz_TX2_Q8_Dot1.source,
    JFz_TX2_Q8_Dot2.source,JFz_TX2_Q8_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q8_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨521203615,116710497⟩,⟨326926486,1325955173⟩⟩,⟨⟨1058957421,1406605859⟩,⟨1514639447,405247914⟩⟩⟩
def h1 : FE := ⟨⟨⟨2094245535,1842588235⟩,⟨933385933,666397148⟩⟩,⟨⟨2104514316,1321045572⟩,⟨1139289773,41827097⟩⟩⟩
def h2 : FE := ⟨⟨⟨480562883,260262765⟩,⟨1817613739,309383605⟩⟩,⟨⟨1845988090,2017633022⟩,⟨730273458,885029070⟩⟩⟩
def h3 : FE := ⟨⟨⟨651948002,1265475081⟩,⟨1644527315,651641650⟩⟩,⟨⟨343027340,134671295⟩,⟨1051841081,959857505⟩⟩⟩
def t2 : FE := ⟨⟨⟨1990793114,1033162024⟩,⟨2036194457,1529653194⟩⟩,⟨⟨1275785047,220078258⟩,⟨2122115797,2132114970⟩⟩⟩
def t1 : FE := ⟨⟨⟨809454908,1998934774⟩,⟨108376462,1382664767⟩⟩,⟨⟨191067704,94991824⟩,⟨164584927,688434362⟩⟩⟩
def value : FE := ⟨⟨⟨1336948798,1302427356⟩,⟨686826955,63018621⟩⟩,⟨⟨1969556263,1062281234⟩,⟨1040474459,830773486⟩⟩⟩
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
end AspisR1.JFz_TX2_Q8_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q8_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q8_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q8_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q8_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q8_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨988443000,1043216615⟩,⟨583704392,1442076853⟩⟩,⟨⟨729137651,998196282⟩,⟨1926632041,1596954375⟩⟩⟩+⟨⟨⟨1540862564,1396231965⟩,⟨1802782081,1825037631⟩⟩,⟨⟨519572978,775379267⟩,⟨293996907,1546458947⟩⟩⟩+⟨⟨⟨2011586006,2048576084⟩,⟨261124963,1691889844⟩⟩,⟨⟨233856251,2025943450⟩,⟨2119730694,1017644047⟩⟩⟩+⟨⟨⟨1838890184,273784618⟩,⟨807578155,344816364⟩⟩,⟨⟨605779157,1826904437⟩,⟨1718198146,1754901581⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1917706209)=h1 := by
  change ((⟨⟨⟨988443000,1043216615⟩,⟨583704392,1442076853⟩⟩,⟨⟨729137651,998196282⟩,⟨1926632041,1596954375⟩⟩⟩-⟨⟨⟨1540862564,1396231965⟩,⟨1802782081,1825037631⟩⟩,⟨⟨519572978,775379267⟩,⟨293996907,1546458947⟩⟩⟩-⟨⟨⟨2011586006,2048576084⟩,⟨261124963,1691889844⟩⟩,⟨⟨233856251,2025943450⟩,⟨2119730694,1017644047⟩⟩⟩+⟨⟨⟨1838890184,273784618⟩,⟨807578155,344816364⟩⟩,⟨⟨605779157,1826904437⟩,⟨1718198146,1754901581⟩⟩⟩)*(536870912*1917706209) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*871377951)=h2 := by
  change ((⟨⟨⟨988443000,1043216615⟩,⟨583704392,1442076853⟩⟩,⟨⟨729137651,998196282⟩,⟨1926632041,1596954375⟩⟩⟩+⟨⟨⟨1540862564,1396231965⟩,⟨1802782081,1825037631⟩⟩,⟨⟨519572978,775379267⟩,⟨293996907,1546458947⟩⟩⟩-⟨⟨⟨2011586006,2048576084⟩,⟨261124963,1691889844⟩⟩,⟨⟨233856251,2025943450⟩,⟨2119730694,1017644047⟩⟩⟩-⟨⟨⟨1838890184,273784618⟩,⟨807578155,344816364⟩⟩,⟨⟨605779157,1826904437⟩,⟨1718198146,1754901581⟩⟩⟩)*(536870912*871377951) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*871377951*1917706209)=h3 := by
  change ((⟨⟨⟨988443000,1043216615⟩,⟨583704392,1442076853⟩⟩,⟨⟨729137651,998196282⟩,⟨1926632041,1596954375⟩⟩⟩-⟨⟨⟨1540862564,1396231965⟩,⟨1802782081,1825037631⟩⟩,⟨⟨519572978,775379267⟩,⟨293996907,1546458947⟩⟩⟩+⟨⟨⟨2011586006,2048576084⟩,⟨261124963,1691889844⟩⟩,⟨⟨233856251,2025943450⟩,⟨2119730694,1017644047⟩⟩⟩-⟨⟨⟨1838890184,273784618⟩,⟨807578155,344816364⟩⟩,⟨⟨605779157,1826904437⟩,⟨1718198146,1754901581⟩⟩⟩)*(536870912*871377951*1917706209) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q8_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q8_CircleNumbers JFz_TX2_Q8_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 871377951=(871377951:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1917706209=(1917706209:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q8_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q8_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q8_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q8_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 871377951)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1917706209)
    (Port5Q1_OpeningValues.values JFz_TX2_Q8_Dots0.value)=JFz_TX2_Q8_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q8_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value18_0.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).x)⁻¹=(871377951 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 2041864042 871377951 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).y)⁻¹=(1917706209 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1797422629 1917706209 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 8) 0#usize=ok selected := JFn_Values18.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 8)
    (JFv_TX2_CircleGeometry.inverse err seed 8)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 8
  rw [x,y,JFz_TX2_Q8_Dots0.source,JFz_TX2_Q8_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q8_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1336948798<2147483647 ∧ 1302427356<2147483647) ∧ (686826955<2147483647 ∧ 63018621<2147483647)) ∧
      ((1969556263<2147483647 ∧ 1062281234<2147483647) ∧ (1040474459<2147483647 ∧ 830773486<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q8_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1336948798,1302427356⟩,⟨686826955,63018621⟩⟩,⟨⟨1969556263,1062281234⟩,⟨1040474459,830773486⟩⟩⟩
def d1 : FE := ⟨⟨⟨808561352,692747672⟩,⟨361546220,1358250188⟩⟩,⟨⟨1110874099,1029653036⟩,⟨2119524575,1885260697⟩⟩⟩
def d2 : FE := ⟨⟨⟨1116855082,137448918⟩,⟨1138851925,2070500897⟩⟩,⟨⟨1549137507,1596122514⟩,⟨137204697,278395007⟩⟩⟩
def d3 : FE := ⟨⟨⟨2006696531,1889902675⟩,⟨1845847409,862601474⟩⟩,⟨⟨579825865,1158804485⟩,⟨792340213,645239520⟩⟩⟩
def c0 : FE := ⟨⟨⟨1130832836,404774836⟩,⟨292935751,674757681⟩⟩,⟨⟨1732033316,1058564976⟩,⟨431352848,910891817⟩⟩⟩
def c1 : FE := ⟨⟨⟨1827134511,1264137125⟩,⟨319942456,2018189649⟩⟩,⟨⟨1159683846,1118470518⟩,⟨114104731,2076746573⟩⟩⟩
def h0 : FE := ⟨⟨⟨780394529,1542502567⟩,⟨1545139039,1088592795⟩⟩,⟨⟨228606610,1748586229⟩,⟨1022385986,1983659001⟩⟩⟩
def h1 : FE := ⟨⟨⟨405241850,1908197804⟩,⟨1380180927,1346473665⟩⟩,⟨⟨1445858581,1088517747⟩,⟨1346470613,1493819195⟩⟩⟩
def h2 : FE := ⟨⟨⟨805961875,1849746627⟩,⟨1393401580,1845270433⟩⟩,⟨⟨2042989814,1497813214⟩,⟨663790712,1984742047⟩⟩⟩
def h3 : FE := ⟨⟨⟨1246577144,727867535⟩,⟨1990406423,529215906⟩⟩,⟨⟨1889909021,1181701918⟩,⟨1593799467,909435472⟩⟩⟩
def t2 : FE := ⟨⟨⟨224700708,1067393740⟩,⟨1753230396,1745983950⟩⟩,⟨⟨206327266,1995597142⟩,⟨140914734,352384084⟩⟩⟩
def t1 : FE := ⟨⟨⟨82078405,1224166274⟩,⟨107480515,1661038832⟩⟩,⟨⟨2100576275,1518806841⟩,⟨1013899232,1430934707⟩⟩⟩
def answer : FE := ⟨⟨⟨1923552449,1893012155⟩,⟨229634491,1383940170⟩⟩,⟨⟨30747705,1448868280⟩,⟨1015275152,946603900⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨1923552449#u32,1893012155#u32⟩,⟨229634491#u32,1383940170#u32⟩⟩,⟨⟨30747705#u32,1448868280#u32⟩,⟨1015275152#u32,946603900#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*1286706960)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*820173713)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1023369884)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1023369884)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).lineX)⁻¹=(1286706960:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1890563306 1286706960 (by norm_num)
theorem cast0 : algebraMap FP FE 1286706960=(1286706960:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).lineY)⁻¹=(820173713:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 67955745 820173713 (by norm_num)
theorem cast1 : algebraMap FP FE 820173713=(820173713:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).lineZ)⁻¹=(1023369884:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1978967902 1023369884 (by norm_num)
theorem cast2 : algebraMap FP FE 1023369884=(1023369884:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 8) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 8) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 8) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 8) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 1286706960) (algebraMap FP FE 820173713) (algebraMap FP FE 1023369884)
    (Port5Q1_OpeningValues.values (JFn_Values.value 8))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 8)
      (JFv_TX2_CircleGeometry.inverse err seed 8)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 8 (JFv_TX2_CircleGeometry.inverse err seed 8)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 8 2,
    JFv_TX2_CircleGeometry.decoded err seed 8 3,
    JFv_TX2_CircleGeometry.decoded err seed 8 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 8).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((1923552449<2147483647 ∧ 1893012155<2147483647) ∧ (229634491<2147483647 ∧ 1383940170<2147483647)) ∧
      ((30747705<2147483647 ∧ 1448868280<2147483647) ∧ (1015275152<2147483647 ∧ 946603900<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q8_Line
end
