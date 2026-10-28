import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q10_Slot0
import NDO_JFz_TX2_Q10_Slot1
import NDO_JFz_TX2_Q10_Slot2
import NDO_JFz_TX2_Q10_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q10_Dot0.value,JFz_TX2_Q10_Dot1.value,JFz_TX2_Q10_Dot2.value,JFz_TX2_Q10_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 10=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q10_Dot0.source,JFz_TX2_Q10_Dot1.source,
    JFz_TX2_Q10_Dot2.source,JFz_TX2_Q10_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q10_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨1006314616,1965196273⟩,⟨293963879,688298164⟩⟩,⟨⟨1850113799,2044821645⟩,⟨1288082092,408800386⟩⟩⟩
def h1 : FE := ⟨⟨⟨1118571388,2054469550⟩,⟨894082132,1480096156⟩⟩,⟨⟨690579645,1907216372⟩,⟨1435106488,1906951725⟩⟩⟩
def h2 : FE := ⟨⟨⟨1839160258,1033905813⟩,⟨893721681,372150139⟩⟩,⟨⟨783245713,2078079776⟩,⟨697428893,364771844⟩⟩⟩
def h3 : FE := ⟨⟨⟨1065472787,179332229⟩,⟨758978172,1518764604⟩⟩,⟨⟨1249007472,800234180⟩,⟨565093190,1167425646⟩⟩⟩
def t2 : FE := ⟨⟨⟨1903350349,1806987431⟩,⟨1616088096,809875153⟩⟩,⟨⟨229944871,1455723148⟩,⟨1835801341,776201565⟩⟩⟩
def t1 : FE := ⟨⟨⟨1157016,1461013340⟩,⟨1918584391,88101301⟩⟩,⟨⟨176880363,748263584⟩,⟨2136126177,1407478381⟩⟩⟩
def value : FE := ⟨⟨⟨1568245334,1686168864⟩,⟨1119134181,1468476285⟩⟩,⟨⟨1798602319,127817939⟩,⟨1344162684,970269715⟩⟩⟩
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
end AspisR1.JFz_TX2_Q10_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q10_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q10_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q10_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q10_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q10_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1034843265,1359224911⟩,⟨672406301,638584879⟩⟩,⟨⟨1674100508,350796033⟩,⟨90890361,857507361⟩⟩⟩+⟨⟨⟨1663637645,423864786⟩,⟨1513689245,640648161⟩⟩,⟨⟨1556710531,1910856093⟩,⟨917389505,395573402⟩⟩⟩+⟨⟨⟨1192495074,1082862451⟩,⟨1171703085,2066339742⟩⟩,⟨⟨1106542019,709388883⟩,⟨264286997,428324940⟩⟩⟩+⟨⟨⟨134282480,699865650⟩,⟨2113024179,1555103521⟩⟩,⟨⟨915618491,913278277⟩,⟨1732277858,2101279488⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1312526128)=h1 := by
  change ((⟨⟨⟨1034843265,1359224911⟩,⟨672406301,638584879⟩⟩,⟨⟨1674100508,350796033⟩,⟨90890361,857507361⟩⟩⟩-⟨⟨⟨1663637645,423864786⟩,⟨1513689245,640648161⟩⟩,⟨⟨1556710531,1910856093⟩,⟨917389505,395573402⟩⟩⟩-⟨⟨⟨1192495074,1082862451⟩,⟨1171703085,2066339742⟩⟩,⟨⟨1106542019,709388883⟩,⟨264286997,428324940⟩⟩⟩+⟨⟨⟨134282480,699865650⟩,⟨2113024179,1555103521⟩⟩,⟨⟨915618491,913278277⟩,⟨1732277858,2101279488⟩⟩⟩)*(536870912*1312526128) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*2134310719)=h2 := by
  change ((⟨⟨⟨1034843265,1359224911⟩,⟨672406301,638584879⟩⟩,⟨⟨1674100508,350796033⟩,⟨90890361,857507361⟩⟩⟩+⟨⟨⟨1663637645,423864786⟩,⟨1513689245,640648161⟩⟩,⟨⟨1556710531,1910856093⟩,⟨917389505,395573402⟩⟩⟩-⟨⟨⟨1192495074,1082862451⟩,⟨1171703085,2066339742⟩⟩,⟨⟨1106542019,709388883⟩,⟨264286997,428324940⟩⟩⟩-⟨⟨⟨134282480,699865650⟩,⟨2113024179,1555103521⟩⟩,⟨⟨915618491,913278277⟩,⟨1732277858,2101279488⟩⟩⟩)*(536870912*2134310719) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*2134310719*1312526128)=h3 := by
  change ((⟨⟨⟨1034843265,1359224911⟩,⟨672406301,638584879⟩⟩,⟨⟨1674100508,350796033⟩,⟨90890361,857507361⟩⟩⟩-⟨⟨⟨1663637645,423864786⟩,⟨1513689245,640648161⟩⟩,⟨⟨1556710531,1910856093⟩,⟨917389505,395573402⟩⟩⟩+⟨⟨⟨1192495074,1082862451⟩,⟨1171703085,2066339742⟩⟩,⟨⟨1106542019,709388883⟩,⟨264286997,428324940⟩⟩⟩-⟨⟨⟨134282480,699865650⟩,⟨2113024179,1555103521⟩⟩,⟨⟨915618491,913278277⟩,⟨1732277858,2101279488⟩⟩⟩)*(536870912*2134310719*1312526128) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q10_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q10_CircleNumbers JFz_TX2_Q10_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2134310719=(2134310719:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1312526128=(1312526128:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q10_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q10_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q10_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q10_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2134310719)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1312526128)
    (Port5Q1_OpeningValues.values JFz_TX2_Q10_Dots0.value)=JFz_TX2_Q10_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q10_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value20_1.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).x)⁻¹=(2134310719 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 746032528 2134310719 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).y)⁻¹=(1312526128 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1917691314 1312526128 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 10) 1#usize=ok selected := JFn_Values20.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 10)
    (JFv_TX2_CircleGeometry.inverse err seed 10)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 10
  rw [x,y,JFz_TX2_Q10_Dots0.source,JFz_TX2_Q10_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q10_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1568245334<2147483647 ∧ 1686168864<2147483647) ∧ (1119134181<2147483647 ∧ 1468476285<2147483647)) ∧
      ((1798602319<2147483647 ∧ 127817939<2147483647) ∧ (1344162684<2147483647 ∧ 970269715<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q10_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q10_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨784635806,290536413⟩,⟨1913427946,1280508549⟩⟩,⟨⟨1205077619,2097471918⟩,⟨1333782330,1893294467⟩⟩⟩
def d1 : FE := ⟨⟨⟨1568245334,1686168864⟩,⟨1119134181,1468476285⟩⟩,⟨⟨1798602319,127817939⟩,⟨1344162684,970269715⟩⟩⟩
def d2 : FE := ⟨⟨⟨831430896,1241285235⟩,⟨1765399785,230690313⟩⟩,⟨⟨1957543568,369620978⟩,⟨174634496,1674182284⟩⟩⟩
def d3 : FE := ⟨⟨⟨1388790482,425601028⟩,⟨930591260,1282365328⟩⟩,⟨⟨1546635047,1004049965⟩,⟨243105753,137849788⟩⟩⟩
def c0 : FE := ⟨⟨⟨1408927173,599723127⟩,⟨2080222692,1868275730⟩⟩,⟨⟨1098121955,1196747692⟩,⟨1847288832,702399142⟩⟩⟩
def c1 : FE := ⟨⟨⟨411256905,71430542⟩,⟨91196408,890983189⟩⟩,⟨⟨233491017,4131131⟩,⟨109964623,1265106612⟩⟩⟩
def h0 : FE := ⟨⟨⟨69533806,910897885⟩,⟨1432138293,528639207⟩⟩,⟨⟨16351903,899740200⟩,⟨237050404,95157240⟩⟩⟩
def h1 : FE := ⟨⟨⟨910092039,1409318658⟩,⟨1085709550,305887636⟩⟩,⟨⟨665806486,1674181235⟩,⟨2052368551,983752877⟩⟩⟩
def h2 : FE := ⟨⟨⟨1971441845,1171781626⟩,⟨716404788,1849211671⟩⟩,⟨⟨724570434,2138971687⟩,⟨1912237582,643864008⟩⟩⟩
def h3 : FE := ⟨⟨⟨1425906919,1182953579⟩,⟨1652381727,1580122828⟩⟩,⟨⟨149925580,1533311096⟩,⟨118453036,1696262282⟩⟩⟩
def t2 : FE := ⟨⟨⟨951042764,1883588839⟩,⟨715847646,1088733984⟩⟩,⟨⟨1339971085,693073176⟩,⟨1053531044,85742757⟩⟩⟩
def t1 : FE := ⟨⟨⟨1754359451,1653661464⟩,⟨980112195,173072017⟩⟩,⟨⟨541982125,410850827⟩,⟨1973009903,1704144593⟩⟩⟩
def answer : FE := ⟨⟨⟨1418767908,875610282⟩,⟨15389388,1881991094⟩⟩,⟨⟨293921443,740020656⟩,⟨1540456159,1426271211⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨1418767908#u32,875610282#u32⟩,⟨15389388#u32,1881991094#u32⟩⟩,⟨⟨293921443#u32,740020656#u32⟩,⟨1540456159#u32,1426271211#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*440467034)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*1930748161)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*2057500775)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*2057500775)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).lineX)⁻¹=(440467034:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 214621191 440467034 (by norm_num)
theorem cast0 : algebraMap FP FE 440467034=(440467034:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).lineY)⁻¹=(1930748161:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 717710175 1930748161 (by norm_num)
theorem cast1 : algebraMap FP FE 1930748161=(1930748161:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).lineZ)⁻¹=(2057500775:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1121887715 2057500775 (by norm_num)
theorem cast2 : algebraMap FP FE 2057500775=(2057500775:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 10) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 10) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 10) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 10) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 440467034) (algebraMap FP FE 1930748161) (algebraMap FP FE 2057500775)
    (Port5Q1_OpeningValues.values (JFn_Values.value 10))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 10)
      (JFv_TX2_CircleGeometry.inverse err seed 10)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 10 (JFv_TX2_CircleGeometry.inverse err seed 10)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 10 2,
    JFv_TX2_CircleGeometry.decoded err seed 10 3,
    JFv_TX2_CircleGeometry.decoded err seed 10 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 10).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((1418767908<2147483647 ∧ 875610282<2147483647) ∧ (15389388<2147483647 ∧ 1881991094<2147483647)) ∧
      ((293921443<2147483647 ∧ 740020656<2147483647) ∧ (1540456159<2147483647 ∧ 1426271211<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q10_Line
end
