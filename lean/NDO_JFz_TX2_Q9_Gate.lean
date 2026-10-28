import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q9_Slot0
import NDO_JFz_TX2_Q9_Slot1
import NDO_JFz_TX2_Q9_Slot2
import NDO_JFz_TX2_Q9_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q9_Dot0.value,JFz_TX2_Q9_Dot1.value,JFz_TX2_Q9_Dot2.value,JFz_TX2_Q9_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 9=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q9_Dot0.source,JFz_TX2_Q9_Dot1.source,
    JFz_TX2_Q9_Dot2.source,JFz_TX2_Q9_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q9_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨1902336684,1098656518⟩,⟨1752126294,1738192942⟩⟩,⟨⟨110808003,1221779572⟩,⟨949901024,2022992545⟩⟩⟩
def h1 : FE := ⟨⟨⟨1255156455,1881258107⟩,⟨1113355475,1854028150⟩⟩,⟨⟨1525626228,425927395⟩,⟨549811190,607891908⟩⟩⟩
def h2 : FE := ⟨⟨⟨1508739564,531338263⟩,⟨453721181,424120818⟩⟩,⟨⟨71264965,1014001631⟩,⟨95767616,1246654569⟩⟩⟩
def h3 : FE := ⟨⟨⟨1624467321,350927485⟩,⟨500215184,2060958000⟩⟩,⟨⟨788086566,2068540679⟩,⟨38056943,2138826313⟩⟩⟩
def t2 : FE := ⟨⟨⟨2087059455,215094886⟩,⟨1090636225,1912405951⟩⟩,⟨⟨1553643404,128526613⟩,⟨725097370,929443539⟩⟩⟩
def t1 : FE := ⟨⟨⟨508916817,135054049⟩,⟨2074571730,1188746053⟩⟩,⟨⟨1059103803,1789560107⟩,⟨1809179936,1037136414⟩⟩⟩
def value : FE := ⟨⟨⟨1739407730,1033905986⟩,⟨397093821,1718230613⟩⟩,⟨⟨2017808454,1510689143⟩,⟨1776877386,557169103⟩⟩⟩
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
end AspisR1.JFz_TX2_Q9_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q9_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q9_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q9_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q9_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q9_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1803040151,439046472⟩,⟨1786184198,407009518⟩⟩,⟨⟨1962504373,1404688130⟩,⟨269387802,555379274⟩⟩⟩+⟨⟨⟨1169102629,136609189⟩,⟨148010991,1994698014⟩⟩,⟨⟨23985727,42975577⟩,⟨973465699,1254491100⟩⟩⟩+⟨⟨⟨1110894591,2135956070⟩,⟨1507100640,498646653⟩⟩,⟨⟨1717755597,309437864⟩,⟨199251691,1955513436⟩⟩⟩+⟨⟨⟨1378825718,1683014341⟩,⟨1419725700,1904933936⟩⟩,⟨⟨1033953609,982533070⟩,⟨210015257,31619076⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1242970229)=h1 := by
  change ((⟨⟨⟨1803040151,439046472⟩,⟨1786184198,407009518⟩⟩,⟨⟨1962504373,1404688130⟩,⟨269387802,555379274⟩⟩⟩-⟨⟨⟨1169102629,136609189⟩,⟨148010991,1994698014⟩⟩,⟨⟨23985727,42975577⟩,⟨973465699,1254491100⟩⟩⟩-⟨⟨⟨1110894591,2135956070⟩,⟨1507100640,498646653⟩⟩,⟨⟨1717755597,309437864⟩,⟨199251691,1955513436⟩⟩⟩+⟨⟨⟨1378825718,1683014341⟩,⟨1419725700,1904933936⟩⟩,⟨⟨1033953609,982533070⟩,⟨210015257,31619076⟩⟩⟩)*(536870912*1242970229) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*2049950052)=h2 := by
  change ((⟨⟨⟨1803040151,439046472⟩,⟨1786184198,407009518⟩⟩,⟨⟨1962504373,1404688130⟩,⟨269387802,555379274⟩⟩⟩+⟨⟨⟨1169102629,136609189⟩,⟨148010991,1994698014⟩⟩,⟨⟨23985727,42975577⟩,⟨973465699,1254491100⟩⟩⟩-⟨⟨⟨1110894591,2135956070⟩,⟨1507100640,498646653⟩⟩,⟨⟨1717755597,309437864⟩,⟨199251691,1955513436⟩⟩⟩-⟨⟨⟨1378825718,1683014341⟩,⟨1419725700,1904933936⟩⟩,⟨⟨1033953609,982533070⟩,⟨210015257,31619076⟩⟩⟩)*(536870912*2049950052) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*2049950052*1242970229)=h3 := by
  change ((⟨⟨⟨1803040151,439046472⟩,⟨1786184198,407009518⟩⟩,⟨⟨1962504373,1404688130⟩,⟨269387802,555379274⟩⟩⟩-⟨⟨⟨1169102629,136609189⟩,⟨148010991,1994698014⟩⟩,⟨⟨23985727,42975577⟩,⟨973465699,1254491100⟩⟩⟩+⟨⟨⟨1110894591,2135956070⟩,⟨1507100640,498646653⟩⟩,⟨⟨1717755597,309437864⟩,⟨199251691,1955513436⟩⟩⟩-⟨⟨⟨1378825718,1683014341⟩,⟨1419725700,1904933936⟩⟩,⟨⟨1033953609,982533070⟩,⟨210015257,31619076⟩⟩⟩)*(536870912*2049950052*1242970229) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q9_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q9_CircleNumbers JFz_TX2_Q9_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2049950052=(2049950052:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1242970229=(1242970229:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q9_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q9_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q9_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q9_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2049950052)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1242970229)
    (Port5Q1_OpeningValues.values JFz_TX2_Q9_Dots0.value)=JFz_TX2_Q9_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q9_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value19_1.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).x)⁻¹=(2049950052 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1643107982 2049950052 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).y)⁻¹=(1242970229 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 704311060 1242970229 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 9) 1#usize=ok selected := JFn_Values19.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 9)
    (JFv_TX2_CircleGeometry.inverse err seed 9)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 9
  rw [x,y,JFz_TX2_Q9_Dots0.source,JFz_TX2_Q9_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q9_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((1739407730<2147483647 ∧ 1033905986<2147483647) ∧ (397093821<2147483647 ∧ 1718230613<2147483647)) ∧
      ((2017808454<2147483647 ∧ 1510689143<2147483647) ∧ (1776877386<2147483647 ∧ 557169103<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q9_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q9_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨295666010,486718680⟩,⟨1088486258,1300289649⟩⟩,⟨⟨631420592,40313731⟩,⟨1271260829,330825150⟩⟩⟩
def d1 : FE := ⟨⟨⟨1739407730,1033905986⟩,⟨397093821,1718230613⟩⟩,⟨⟨2017808454,1510689143⟩,⟨1776877386,557169103⟩⟩⟩
def d2 : FE := ⟨⟨⟨1755286952,56799981⟩,⟨970306746,1862977856⟩⟩,⟨⟨635210495,728242439⟩,⟨637094972,841182003⟩⟩⟩
def d3 : FE := ⟨⟨⟨1460124800,178026518⟩,⟨1230459742,1596807589⟩⟩,⟨⟨736291746,2010145050⟩,⟨1010173706,1855023846⟩⟩⟩
def c0 : FE := ⟨⟨⟨1848656652,641099504⟩,⟨853587734,346679121⟩⟩,⟨⟨715460,1377417611⟩,⟨427388611,467532509⟩⟩⟩
def c1 : FE := ⟨⟨⟨1795628415,1506544321⟩,⟨1037051416,425360622⟩⟩,⟨⟨1988626645,606637933⟩,⟨5909041,439507758⟩⟩⟩
def h0 : FE := ⟨⟨⟨1312621373,975733703⟩,⟨384715730,1082705515⟩⟩,⟨⟨468311910,535476679⟩,⟨1710722635,1969791849⟩⟩⟩
def h1 : FE := ⟨⟨⟨748400710,80089⟩,⟨945319575,1459761695⟩⟩,⟨⟨2068412876,992027772⟩,⟨216648826,1527261957⟩⟩⟩
def h2 : FE := ⟨⟨⟨771587354,1610190849⟩,⟨1464255635,61825835⟩⟩,⟨⟨584560602,1201867655⟩,⟨1450606447,1966028142⟩⟩⟩
def h3 : FE := ⟨⟨⟨543770758,1025818122⟩,⟨1373902218,1159365741⟩⟩,⟨⟨1083242980,1367557337⟩,⟨1299075269,440062175⟩⟩⟩
def t2 : FE := ⟨⟨⟨994187453,443564027⟩,⟨735624589,1354919906⟩⟩,⟨⟨1978290757,828525434⟩,⟨1086692518,522546481⟩⟩⟩
def t1 : FE := ⟨⟨⟨1508304676,147518112⟩,⟨1934708256,801179684⟩⟩,⟨⟨1102150377,1588154638⟩,⟨1242163186,1137918643⟩⟩⟩
def answer : FE := ⟨⟨⟨1972129685,232942795⟩,⟨498840605,1438222756⟩⟩,⟨⟨412733223,1961776441⟩,⟨743418827,802783139⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨1972129685#u32,232942795#u32⟩,⟨498840605#u32,1438222756#u32⟩⟩,⟨⟨412733223#u32,1961776441#u32⟩,⟨743418827#u32,802783139#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*1422199420)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*196676174)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1868447787)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1868447787)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).lineX)⁻¹=(1422199420:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 271977808 1422199420 (by norm_num)
theorem cast0 : algebraMap FP FE 1422199420=(1422199420:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).lineY)⁻¹=(196676174:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1772899931 196676174 (by norm_num)
theorem cast1 : algebraMap FP FE 196676174=(196676174:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).lineZ)⁻¹=(1868447787:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1090365005 1868447787 (by norm_num)
theorem cast2 : algebraMap FP FE 1868447787=(1868447787:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 9) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 9) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 9) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 9) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 1422199420) (algebraMap FP FE 196676174) (algebraMap FP FE 1868447787)
    (Port5Q1_OpeningValues.values (JFn_Values.value 9))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 9)
      (JFv_TX2_CircleGeometry.inverse err seed 9)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 9 (JFv_TX2_CircleGeometry.inverse err seed 9)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 9 2,
    JFv_TX2_CircleGeometry.decoded err seed 9 3,
    JFv_TX2_CircleGeometry.decoded err seed 9 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 9).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((1972129685<2147483647 ∧ 232942795<2147483647) ∧ (498840605<2147483647 ∧ 1438222756<2147483647)) ∧
      ((412733223<2147483647 ∧ 1961776441<2147483647) ∧ (743418827<2147483647 ∧ 802783139<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q9_Line
end
