import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q2_Slot0
import NDO_JFz_TX2_Q2_Slot1
import NDO_JFz_TX2_Q2_Slot2
import NDO_JFz_TX2_Q2_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q2_Dot0.value,JFz_TX2_Q2_Dot1.value,JFz_TX2_Q2_Dot2.value,JFz_TX2_Q2_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 2=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q2_Dot0.source,JFz_TX2_Q2_Dot1.source,
    JFz_TX2_Q2_Dot2.source,JFz_TX2_Q2_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q2_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨37931794,1361953449⟩,⟨1283810900,2030383567⟩⟩,⟨⟨1337861583,842311803⟩,⟨1340755339,1695996463⟩⟩⟩
def h1 : FE := ⟨⟨⟨1388450480,1647916546⟩,⟨1927389872,1304185287⟩⟩,⟨⟨932935756,742723620⟩,⟨2105333312,89099778⟩⟩⟩
def h2 : FE := ⟨⟨⟨1179409592,1617400655⟩,⟨2052422923,784718608⟩⟩,⟨⟨193393738,112076512⟩,⟨2144618516,474495833⟩⟩⟩
def h3 : FE := ⟨⟨⟨399628253,2000426903⟩,⟨340573331,1456332346⟩⟩,⟨⟨764558215,1675328272⟩,⟨1907660954,259089885⟩⟩⟩
def t2 : FE := ⟨⟨⟨118251375,168453604⟩,⟨2086475107,477077959⟩⟩,⟨⟨1610487417,591887478⟩,⟨1105282805,962944901⟩⟩⟩
def t1 : FE := ⟨⟨⟨923389653,1102674527⟩,⟨2067082626,857804228⟩⟩,⟨⟨12430612,1991817881⟩,⟨903289465,1699995390⟩⟩⟩
def value : FE := ⟨⟨⟨1236058983,1842326522⟩,⟨1081455735,2070829967⟩⟩,⟨⟨431836317,1306907118⟩,⟨2005005026,1786518228⟩⟩⟩
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
end AspisR1.JFz_TX2_Q2_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q2_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q2_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q2_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q2_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q2_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1137268559,603602611⟩,⟨1361665774,763003791⟩⟩,⟨⟨1761481573,845378202⟩,⟨1667587975,217560771⟩⟩⟩+⟨⟨⟨1073154022,1360712262⟩,⟨263089029,1489463568⟩⟩,⟨⟨1531961048,1158874901⟩,⟨1340212447,232046220⟩⟩⟩+⟨⟨⟨1923734971,1873897209⟩,⟨954978993,57231872⟩⟩,⟨⟨262176034,28573406⟩,⟨203049178,100396934⟩⟩⟩+⟨⟨⟨312536918,1609601714⟩,⟨408026157,1516867743⟩⟩,⟨⟨1795827677,1336420703⟩,⟨4688109,1939014633⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*724951755)=h1 := by
  change ((⟨⟨⟨1137268559,603602611⟩,⟨1361665774,763003791⟩⟩,⟨⟨1761481573,845378202⟩,⟨1667587975,217560771⟩⟩⟩-⟨⟨⟨1073154022,1360712262⟩,⟨263089029,1489463568⟩⟩,⟨⟨1531961048,1158874901⟩,⟨1340212447,232046220⟩⟩⟩-⟨⟨⟨1923734971,1873897209⟩,⟨954978993,57231872⟩⟩,⟨⟨262176034,28573406⟩,⟨203049178,100396934⟩⟩⟩+⟨⟨⟨312536918,1609601714⟩,⟨408026157,1516867743⟩⟩,⟨⟨1795827677,1336420703⟩,⟨4688109,1939014633⟩⟩⟩)*(536870912*724951755) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*1147550096)=h2 := by
  change ((⟨⟨⟨1137268559,603602611⟩,⟨1361665774,763003791⟩⟩,⟨⟨1761481573,845378202⟩,⟨1667587975,217560771⟩⟩⟩+⟨⟨⟨1073154022,1360712262⟩,⟨263089029,1489463568⟩⟩,⟨⟨1531961048,1158874901⟩,⟨1340212447,232046220⟩⟩⟩-⟨⟨⟨1923734971,1873897209⟩,⟨954978993,57231872⟩⟩,⟨⟨262176034,28573406⟩,⟨203049178,100396934⟩⟩⟩-⟨⟨⟨312536918,1609601714⟩,⟨408026157,1516867743⟩⟩,⟨⟨1795827677,1336420703⟩,⟨4688109,1939014633⟩⟩⟩)*(536870912*1147550096) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*1147550096*724951755)=h3 := by
  change ((⟨⟨⟨1137268559,603602611⟩,⟨1361665774,763003791⟩⟩,⟨⟨1761481573,845378202⟩,⟨1667587975,217560771⟩⟩⟩-⟨⟨⟨1073154022,1360712262⟩,⟨263089029,1489463568⟩⟩,⟨⟨1531961048,1158874901⟩,⟨1340212447,232046220⟩⟩⟩+⟨⟨⟨1923734971,1873897209⟩,⟨954978993,57231872⟩⟩,⟨⟨262176034,28573406⟩,⟨203049178,100396934⟩⟩⟩-⟨⟨⟨312536918,1609601714⟩,⟨408026157,1516867743⟩⟩,⟨⟨1795827677,1336420703⟩,⟨4688109,1939014633⟩⟩⟩)*(536870912*1147550096*724951755) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q2_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q2_CircleNumbers JFz_TX2_Q2_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1147550096=(1147550096:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 724951755=(724951755:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q2_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q2_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q2_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q2_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1147550096)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 724951755)
    (Port5Q1_OpeningValues.values JFz_TX2_Q2_Dots0.value)=JFz_TX2_Q2_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q2_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value12_0.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).x)⁻¹=(1147550096 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1517732261 1147550096 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).y)⁻¹=(724951755 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 2003432416 724951755 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 2) 0#usize=ok selected := JFn_Values12.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 2)
    (JFv_TX2_CircleGeometry.inverse err seed 2)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 2
  rw [x,y,JFz_TX2_Q2_Dots0.source,JFz_TX2_Q2_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q2_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1236058983<2147483647 ∧ 1842326522<2147483647) ∧ (1081455735<2147483647 ∧ 2070829967<2147483647)) ∧
      ((431836317<2147483647 ∧ 1306907118<2147483647) ∧ (2005005026<2147483647 ∧ 1786518228<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q2_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q2_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1236058983,1842326522⟩,⟨1081455735,2070829967⟩⟩,⟨⟨431836317,1306907118⟩,⟨2005005026,1786518228⟩⟩⟩
def d1 : FE := ⟨⟨⟨443387557,1380048824⟩,⟨1903557389,1021714701⟩⟩,⟨⟨168124661,1626022350⟩,⟨1551893939,1880490507⟩⟩⟩
def d2 : FE := ⟨⟨⟨1390886039,701673580⟩,⟨1560804679,978778748⟩⟩,⟨⟨355003022,1354583439⟩,⟨688667057,830534546⟩⟩⟩
def d3 : FE := ⟨⟨⟨594041695,590716042⟩,⟨1643204674,854254936⟩⟩,⟨⟨2096853037,1634326218⟩,⟨1235016825,1673069921⟩⟩⟩
def c0 : FE := ⟨⟨⟨1865944591,1241033109⟩,⟨1885320541,1234495625⟩⟩,⟨⟨446121907,1132979579⟩,⟨495031076,1857988300⟩⟩⟩
def c1 : FE := ⟨⟨⟨1082445180,888409593⟩,⟨221892889,43796446⟩⟩,⟨⟨1384661099,379141104⟩,⟨1917420305,1319444456⟩⟩⟩
def h0 : FE := ⟨⟨⟨1989835392,1128691242⟩,⟨2084126531,1231394588⟩⟩,⟨⟨1299825171,2017330693⟩,⟨833274800,468911477⟩⟩⟩
def h1 : FE := ⟨⟨⟨400453062,1064721351⟩,⟨1053606715,1712887859⟩⟩,⟨⟨915391503,1829802165⟩,⟨132483867,1588716378⟩⟩⟩
def h2 : FE := ⟨⟨⟨461887448,2057017887⟩,⟨991910810,398409625⟩⟩,⟨⟨1950604256,1165758620⟩,⟨124399027,30009857⟩⟩⟩
def h3 : FE := ⟨⟨⟨297113309,1391433346⟩,⟨1338490138,1655452750⟩⟩,⟨⟨424359379,193162743⟩,⟨1001854964,257770781⟩⟩⟩
def t2 : FE := ⟨⟨⟨1903540212,420014704⟩,⟨1777147100,469636926⟩⟩,⟨⟨2127484149,618925614⟩,⟨1425590732,824821913⟩⟩⟩
def t1 : FE := ⟨⟨⟨1586501139,1837160482⟩,⟨486909116,62779511⟩⟩,⟨⟨449563193,126133075⟩,⟨1191887101,199093863⟩⟩⟩
def answer : FE := ⟨⟨⟨876902741,1341473368⟩,⟨186399591,735677590⟩⟩,⟨⟨813832716,1314210122⟩,⟨1740475688,1831261998⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨876902741#u32,1341473368#u32⟩,⟨186399591#u32,735677590#u32⟩⟩,⟨⟨813832716#u32,1314210122#u32⟩,⟨1740475688#u32,1831261998#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*2113554143)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*689703930)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*715459030)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*715459030)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).lineX)⁻¹=(2113554143:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 889931182 2113554143 (by norm_num)
theorem cast0 : algebraMap FP FE 2113554143=(2113554143:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).lineY)⁻¹=(689703930:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1416187298 689703930 (by norm_num)
theorem cast1 : algebraMap FP FE 689703930=(689703930:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).lineZ)⁻¹=(715459030:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1674392043 715459030 (by norm_num)
theorem cast2 : algebraMap FP FE 715459030=(715459030:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 2) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 2) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 2) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 2) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 2113554143) (algebraMap FP FE 689703930) (algebraMap FP FE 715459030)
    (Port5Q1_OpeningValues.values (JFn_Values.value 2))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 2)
      (JFv_TX2_CircleGeometry.inverse err seed 2)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 2 (JFv_TX2_CircleGeometry.inverse err seed 2)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 2 2,
    JFv_TX2_CircleGeometry.decoded err seed 2 3,
    JFv_TX2_CircleGeometry.decoded err seed 2 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 2).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((876902741<2147483647 ∧ 1341473368<2147483647) ∧ (186399591<2147483647 ∧ 735677590<2147483647)) ∧
      ((813832716<2147483647 ∧ 1314210122<2147483647) ∧ (1740475688<2147483647 ∧ 1831261998<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q2_Line
end
