import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q11_Slot0
import NDO_JFz_TX2_Q11_Slot1
import NDO_JFz_TX2_Q11_Slot2
import NDO_JFz_TX2_Q11_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q11_Dot0.value,JFz_TX2_Q11_Dot1.value,JFz_TX2_Q11_Dot2.value,JFz_TX2_Q11_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 11=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q11_Dot0.source,JFz_TX2_Q11_Dot1.source,
    JFz_TX2_Q11_Dot2.source,JFz_TX2_Q11_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q11_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨571377852,1073125868⟩,⟨1178234195,1844946313⟩⟩,⟨⟨1295183621,645853562⟩,⟨1967937645,224600977⟩⟩⟩
def h1 : FE := ⟨⟨⟨59060216,1506648213⟩,⟨1571378738,885776274⟩⟩,⟨⟨1423279828,1528217438⟩,⟨1813256814,1880769814⟩⟩⟩
def h2 : FE := ⟨⟨⟨138268333,393894453⟩,⟨1813468209,1588108105⟩⟩,⟨⟨543449150,1876411863⟩,⟨1023270502,374617741⟩⟩⟩
def h3 : FE := ⟨⟨⟨317476357,524247733⟩,⟨637688788,526988579⟩⟩,⟨⟨326744037,1924980918⟩,⟨105387804,750236560⟩⟩⟩
def t2 : FE := ⟨⟨⟨370590995,380446962⟩,⟨1872535669,1961112278⟩⟩,⟨⟨140521188,1449177661⟩,⟨1244070717,1674156679⟩⟩⟩
def t1 : FE := ⟨⟨⟨1251593115,1485121049⟩,⟨697262062,1055977865⟩⟩,⟨⟨1058937514,1111239748⟩,⟨1749905959,615338552⟩⟩⟩
def value : FE := ⟨⟨⟨1411296291,1129162310⟩,⟨1767170202,1284306876⟩⟩,⟨⟨496133548,1977234611⟩,⟨1645476028,1815489495⟩⟩⟩
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
end AspisR1.JFz_TX2_Q11_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q11_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q11_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q11_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q11_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q11_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨942847371,1350928017⟩,⟨98213579,79470031⟩⟩,⟨⟨1296849213,1898168300⟩,⟨610228297,327296542⟩⟩⟩+⟨⟨⟨1190052300,1094237567⟩,⟨996126046,1385379076⟩⟩,⟨⟨1791524238,392674102⟩,⟨1277631567,683562297⟩⟩⟩+⟨⟨⟨1442197263,1376685721⟩,⟨305191943,1608452878⟩⟩,⟨⟨1579785464,2138749225⟩,⟨1432256771,1890141081⟩⟩⟩+⟨⟨⟨857898121,470652167⟩,⟨1165921565,11515973⟩⟩,⟨⟨512575569,301306268⟩,⟨256666651,144887635⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1927375507)=h1 := by
  change ((⟨⟨⟨942847371,1350928017⟩,⟨98213579,79470031⟩⟩,⟨⟨1296849213,1898168300⟩,⟨610228297,327296542⟩⟩⟩-⟨⟨⟨1190052300,1094237567⟩,⟨996126046,1385379076⟩⟩,⟨⟨1791524238,392674102⟩,⟨1277631567,683562297⟩⟩⟩-⟨⟨⟨1442197263,1376685721⟩,⟨305191943,1608452878⟩⟩,⟨⟨1579785464,2138749225⟩,⟨1432256771,1890141081⟩⟩⟩+⟨⟨⟨857898121,470652167⟩,⟨1165921565,11515973⟩⟩,⟨⟨512575569,301306268⟩,⟨256666651,144887635⟩⟩⟩)*(536870912*1927375507) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*775620002)=h2 := by
  change ((⟨⟨⟨942847371,1350928017⟩,⟨98213579,79470031⟩⟩,⟨⟨1296849213,1898168300⟩,⟨610228297,327296542⟩⟩⟩+⟨⟨⟨1190052300,1094237567⟩,⟨996126046,1385379076⟩⟩,⟨⟨1791524238,392674102⟩,⟨1277631567,683562297⟩⟩⟩-⟨⟨⟨1442197263,1376685721⟩,⟨305191943,1608452878⟩⟩,⟨⟨1579785464,2138749225⟩,⟨1432256771,1890141081⟩⟩⟩-⟨⟨⟨857898121,470652167⟩,⟨1165921565,11515973⟩⟩,⟨⟨512575569,301306268⟩,⟨256666651,144887635⟩⟩⟩)*(536870912*775620002) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*775620002*1927375507)=h3 := by
  change ((⟨⟨⟨942847371,1350928017⟩,⟨98213579,79470031⟩⟩,⟨⟨1296849213,1898168300⟩,⟨610228297,327296542⟩⟩⟩-⟨⟨⟨1190052300,1094237567⟩,⟨996126046,1385379076⟩⟩,⟨⟨1791524238,392674102⟩,⟨1277631567,683562297⟩⟩⟩+⟨⟨⟨1442197263,1376685721⟩,⟨305191943,1608452878⟩⟩,⟨⟨1579785464,2138749225⟩,⟨1432256771,1890141081⟩⟩⟩-⟨⟨⟨857898121,470652167⟩,⟨1165921565,11515973⟩⟩,⟨⟨512575569,301306268⟩,⟨256666651,144887635⟩⟩⟩)*(536870912*775620002*1927375507) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q11_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q11_CircleNumbers JFz_TX2_Q11_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 775620002=(775620002:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1927375507=(1927375507:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q11_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q11_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q11_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q11_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 775620002)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1927375507)
    (Port5Q1_OpeningValues.values JFz_TX2_Q11_Dots0.value)=JFz_TX2_Q11_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q11_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value21_1.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).x)⁻¹=(775620002 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 222477309 775620002 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).y)⁻¹=(1927375507 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 611065806 1927375507 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 11) 1#usize=ok selected := JFn_Values21.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 11)
    (JFv_TX2_CircleGeometry.inverse err seed 11)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 11
  rw [x,y,JFz_TX2_Q11_Dots0.source,JFz_TX2_Q11_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q11_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1411296291<2147483647 ∧ 1129162310<2147483647) ∧ (1767170202<2147483647 ∧ 1284306876<2147483647)) ∧
      ((496133548<2147483647 ∧ 1977234611<2147483647) ∧ (1645476028<2147483647 ∧ 1815489495<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q11_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q11_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1497554691,668726392⟩,⟨520250570,1887651521⟩⟩,⟨⟨1081528606,2055159448⟩,⟨1086773736,353720130⟩⟩⟩
def d1 : FE := ⟨⟨⟨1411296291,1129162310⟩,⟨1767170202,1284306876⟩⟩,⟨⟨496133548,1977234611⟩,⟨1645476028,1815489495⟩⟩⟩
def d2 : FE := ⟨⟨⟨441812814,1646979782⟩,⟨1581765854,1438752447⟩⟩,⟨⟨142547598,1844055308⟩,⟨2092214594,1236184248⟩⟩⟩
def d3 : FE := ⟨⟨⟨625005061,370892791⟩,⟨605294985,1162391965⟩⟩,⟨⟨1065120480,516537978⟩,⟨1164913007,1025216952⟩⟩⟩
def c0 : FE := ⟨⟨⟨1310899474,1623326925⟩,⟨117095243,1992072779⟩⟩,⟨⟨2097399903,764335238⟩,⟨453652607,1377224474⟩⟩⟩
def c1 : FE := ⟨⟨⟨2068413084,35403831⟩,⟨1103658858,1771396487⟩⟩,⟨⟨1025023422,720864809⟩,⟨247532586,757969984⟩⟩⟩
def h0 : FE := ⟨⟨⟨1530788126,417069407⟩,⟨581749491,1980146614⟩⟩,⟨⟨696332558,2135117748⟩,⟨2034215253,1644523618⟩⟩⟩
def h1 : FE := ⟨⟨⟨1689656279,829365378⟩,⟨1684118874,1881734633⟩⟩,⟨⟨487469839,1816341847⟩,⟨1424334420,1067597229⟩⟩⟩
def h2 : FE := ⟨⟨⟨2017043169,904705356⟩,⟨817101627,2074862399⟩⟩,⟨⟨1495766055,300118370⟩,⟨1629362395,2144666888⟩⟩⟩
def h3 : FE := ⟨⟨⟨1197924857,361435787⟩,⟨1740053317,733406004⟩⟩,⟨⟨70296062,1153375394⟩,⟨1022982049,617313835⟩⟩⟩
def t2 : FE := ⟨⟨⟨516844968,515722042⟩,⟨1771564690,1969220692⟩⟩,⟨⟨1086670726,1282667052⟩,⟨109562159,719040579⟩⟩⟩
def t1 : FE := ⟨⟨⟨747656903,481644506⟩,⟨626795347,140929053⟩⟩,⟨⟨1132944214,186910043⟩,⟨671628809,246976693⟩⟩⟩
def answer : FE := ⟨⟨⟨2027874762,1273831261⟩,⟨1321676290,682618528⟩⟩,⟨⟨1949451629,108903828⟩,⟨674543805,57690103⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨2027874762#u32,1273831261#u32⟩,⟨1321676290#u32,682618528#u32⟩⟩,⟨⟨1949451629#u32,108903828#u32⟩,⟨674543805#u32,57690103#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*333339591)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*512533924)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*545012488)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*545012488)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).lineX)⁻¹=(333339591:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 675376634 333339591 (by norm_num)
theorem cast0 : algebraMap FP FE 333339591=(333339591:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).lineY)⁻¹=(512533924:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1307689502 512533924 (by norm_num)
theorem cast1 : algebraMap FP FE 512533924=(512533924:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).lineZ)⁻¹=(545012488:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1773649059 545012488 (by norm_num)
theorem cast2 : algebraMap FP FE 545012488=(545012488:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 11) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 11) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 11) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 11) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 333339591) (algebraMap FP FE 512533924) (algebraMap FP FE 545012488)
    (Port5Q1_OpeningValues.values (JFn_Values.value 11))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 11)
      (JFv_TX2_CircleGeometry.inverse err seed 11)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 11 (JFv_TX2_CircleGeometry.inverse err seed 11)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 11 2,
    JFv_TX2_CircleGeometry.decoded err seed 11 3,
    JFv_TX2_CircleGeometry.decoded err seed 11 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 11).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((2027874762<2147483647 ∧ 1273831261<2147483647) ∧ (1321676290<2147483647 ∧ 682618528<2147483647)) ∧
      ((1949451629<2147483647 ∧ 108903828<2147483647) ∧ (674543805<2147483647 ∧ 57690103<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q11_Line
end
