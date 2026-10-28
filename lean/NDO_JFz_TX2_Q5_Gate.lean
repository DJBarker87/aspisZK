import NDO_JFw_TX2_CircleNumbers
import NDO_JFn_Lines
import NDO_JFz_TX2_Q5_Slot0
import NDO_JFz_TX2_Q5_Slot1
import NDO_JFz_TX2_Q5_Slot2
import NDO_JFz_TX2_Q5_Slot3
import NDO_JFv_TX2_Query0Formula
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q5_Dot0.value,JFz_TX2_Q5_Dot1.value,JFz_TX2_Q5_Dot2.value,JFz_TX2_Q5_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 5=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q5_Dot0.source,JFz_TX2_Q5_Dot1.source,
    JFz_TX2_Q5_Dot2.source,JFz_TX2_Q5_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q5_Dots0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨360062902,451931830⟩,⟨1088366486,561719659⟩⟩,⟨⟨1667378946,1270772913⟩,⟨1715801958,1602761615⟩⟩⟩
def h1 : FE := ⟨⟨⟨1379631222,1344278117⟩,⟨430190025,1438112234⟩⟩,⟨⟨1057725729,1920428188⟩,⟨854460283,1896101513⟩⟩⟩
def h2 : FE := ⟨⟨⟨120460428,2007422810⟩,⟨1702936582,1196267847⟩⟩,⟨⟨1421796928,257942617⟩,⟨89396028,630056747⟩⟩⟩
def h3 : FE := ⟨⟨⟨468838050,1914346065⟩,⟨1460105907,763200885⟩⟩,⟨⟨1781787948,1450669214⟩,⟨1401263682,446728695⟩⟩⟩
def t2 : FE := ⟨⟨⟨786500215,868986989⟩,⟨1181760570,749529919⟩⟩,⟨⟨1564459103,123920448⟩,⟨639281939,2115496105⟩⟩⟩
def t1 : FE := ⟨⟨⟨1782445560,590365353⟩,⟨399476955,867896017⟩⟩,⟨⟨262064318,2000436684⟩,⟨1308993732,896284384⟩⟩⟩
def value : FE := ⟨⟨⟨525804773,383663845⟩,⟨2054336180,977361562⟩⟩,⟨⟨2145639217,2006113668⟩,⟨1042851790,746334419⟩⟩⟩
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
end AspisR1.JFz_TX2_Q5_CircleNumbers
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFz_TX2_Q5_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q5_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q5_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q5_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFz_TX2_Q5_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨172594310,1497858654⟩,⟨856139292,1003679228⟩⟩,⟨⟨718956194,556380440⟩,⟨831226019,1469423122⟩⟩⟩+⟨⟨⟨410048904,579404399⟩,⟨1834347943,993756298⟩⟩,⟨⟨2114862643,201986180⟩,⟨844054523,736108193⟩⟩⟩+⟨⟨⟨330673103,304892309⟩,⟨523500546,3519463⟩⟩,⟨⟨777372528,435632527⟩,⟨770006018,1782713068⟩⟩⟩+⟨⟨⟨526935291,1573055605⟩,⟨1139478163,245923647⟩⟩,⟨⟨910840772,1741608858⟩,⟨122953978,275318430⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*739406461)=h1 := by
  change ((⟨⟨⟨172594310,1497858654⟩,⟨856139292,1003679228⟩⟩,⟨⟨718956194,556380440⟩,⟨831226019,1469423122⟩⟩⟩-⟨⟨⟨410048904,579404399⟩,⟨1834347943,993756298⟩⟩,⟨⟨2114862643,201986180⟩,⟨844054523,736108193⟩⟩⟩-⟨⟨⟨330673103,304892309⟩,⟨523500546,3519463⟩⟩,⟨⟨777372528,435632527⟩,⟨770006018,1782713068⟩⟩⟩+⟨⟨⟨526935291,1573055605⟩,⟨1139478163,245923647⟩⟩,⟨⟨910840772,1741608858⟩,⟨122953978,275318430⟩⟩⟩)*(536870912*739406461) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*952829633)=h2 := by
  change ((⟨⟨⟨172594310,1497858654⟩,⟨856139292,1003679228⟩⟩,⟨⟨718956194,556380440⟩,⟨831226019,1469423122⟩⟩⟩+⟨⟨⟨410048904,579404399⟩,⟨1834347943,993756298⟩⟩,⟨⟨2114862643,201986180⟩,⟨844054523,736108193⟩⟩⟩-⟨⟨⟨330673103,304892309⟩,⟨523500546,3519463⟩⟩,⟨⟨777372528,435632527⟩,⟨770006018,1782713068⟩⟩⟩-⟨⟨⟨526935291,1573055605⟩,⟨1139478163,245923647⟩⟩,⟨⟨910840772,1741608858⟩,⟨122953978,275318430⟩⟩⟩)*(536870912*952829633) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*952829633*739406461)=h3 := by
  change ((⟨⟨⟨172594310,1497858654⟩,⟨856139292,1003679228⟩⟩,⟨⟨718956194,556380440⟩,⟨831226019,1469423122⟩⟩⟩-⟨⟨⟨410048904,579404399⟩,⟨1834347943,993756298⟩⟩,⟨⟨2114862643,201986180⟩,⟨844054523,736108193⟩⟩⟩+⟨⟨⟨330673103,304892309⟩,⟨523500546,3519463⟩⟩,⟨⟨777372528,435632527⟩,⟨770006018,1782713068⟩⟩⟩-⟨⟨⟨526935291,1573055605⟩,⟨1139478163,245923647⟩⟩,⟨⟨910840772,1741608858⟩,⟨122953978,275318430⟩⟩⟩)*(536870912*952829633*739406461) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
end AspisR1.JFz_TX2_Q5_CircleCoefficients
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q5_CircleNumbers JFz_TX2_Q5_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 952829633=(952829633:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 739406461=(739406461:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q5_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q5_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q5_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q5_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 952829633)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 739406461)
    (Port5Q1_OpeningValues.values JFz_TX2_Q5_Dots0.value)=JFz_TX2_Q5_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q5_CircleFormula
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Query
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value15_2.value
theorem x : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).x)⁻¹=(952829633 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1444421623 952829633 (by norm_num)
#print axioms x
theorem y : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).y)⁻¹=(739406461 : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 654734402 739406461 (by norm_num)
#print axioms y
theorem selected_read : Array.index_usize (JFn_Values.value 5) 2#usize=ok selected := JFn_Values15.selected

def Goal {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value 5)
    (JFv_TX2_CircleGeometry.inverse err seed 5)=ok selected

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed 5
  rw [x,y,JFz_TX2_Q5_Dots0.source,JFz_TX2_Q5_CircleFormula.formula] at sem
  have selectedValue : JFz_TX2_Q5_CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((525804773<2147483647 ∧ 383663845<2147483647) ∧ (2054336180<2147483647 ∧ 977361562<2147483647)) ∧
      ((2145639217<2147483647 ∧ 2006113668<2147483647) ∧ (1042851790<2147483647 ∧ 746334419<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.JFz_TX2_Q5_Query
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1749639170,1290136797⟩,⟨221955118,583088708⟩⟩,⟨⟨454101661,30355175⟩,⟨1908354380,1743188521⟩⟩⟩
def d1 : FE := ⟨⟨⟨2125733106,1095027047⟩,⟨2055831088,1391136258⟩⟩,⟨⟨2135643119,539335121⟩,⟨24058997,1962945445⟩⟩⟩
def d2 : FE := ⟨⟨⟨525804773,383663845⟩,⟨2054336180,977361562⟩⟩,⟨⟨2145639217,2006113668⟩,⟨1042851790,746334419⟩⟩⟩
def d3 : FE := ⟨⟨⟨770560448,1880496115⟩,⟨912993931,2090132334⟩⟩,⟨⟨846412175,827636172⟩,⟨105495798,1533028336⟩⟩⟩
def c0 : FE := ⟨⟨⟨735711825,560074535⟩,⟨1524571425,1115517266⟩⟩,⟨⟨2044245268,1667434425⟩,⟨125313301,1764508368⟩⟩⟩
def c1 : FE := ⟨⟨⟨2102407265,1309622934⟩,⟨1826570842,817280516⟩⟩,⟨⟨1084379713,514458916⟩,⟨2114752771,412899458⟩⟩⟩
def h0 : FE := ⟨⟨⟨1829805286,1162330951⟩,⟨1848149991,186687892⟩⟩,⟨⟨1395449043,850860034⟩,⟨1307061153,2033245092⟩⟩⟩
def h1 : FE := ⟨⟨⟨1419059545,2008590558⟩,⟨601829310,966398891⟩⟩,⟨⟨490570667,17204847⟩,⟨1120033036,1088703913⟩⟩⟩
def h2 : FE := ⟨⟨⟨990540334,1913803213⟩,⟨1479120454,2136703577⟩⟩,⟨⟨128882806,1889961288⟩,⟨1611376356,116822116⟩⟩⟩
def h3 : FE := ⟨⟨⟨210281016,1504015741⟩,⟨57882231,1948030851⟩⟩,⟨⟨243591838,2022602135⟩,⟨554637738,1626699483⟩⟩⟩
def t2 : FE := ⟨⟨⟨1718775089,927247435⟩,⟨1492110075,1643006542⟩⟩,⟨⟨1994893997,1453124554⟩,⟨484769251,20371187⟩⟩⟩
def t1 : FE := ⟨⟨⟨991377426,1650721772⟩,⟨1767932592,376844911⟩⟩,⟨⟨677633668,1486337757⟩,⟨1153686014,603821853⟩⟩⟩
def answer : FE := ⟨⟨⟨1935845750,472381860⟩,⟨678537224,236705647⟩⟩,⟨⟨120292263,1606675882⟩,⟨137257660,247347224⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨1935845750#u32,472381860#u32⟩,⟨678537224#u32,236705647#u32⟩⟩,⟨⟨120292263#u32,1606675882#u32⟩,⟨137257660#u32,247347224#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*1365107723)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*1782692429)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1654881114)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1654881114)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).lineX)⁻¹=(1365107723:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1216629377 1365107723 (by norm_num)
theorem cast0 : algebraMap FP FE 1365107723=(1365107723:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).lineY)⁻¹=(1782692429:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 529768542 1782692429 (by norm_num)
theorem cast1 : algebraMap FP FE 1782692429=(1782692429:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).lineZ)⁻¹=(1654881114:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1201169175 1654881114 (by norm_num)
theorem cast2 : algebraMap FP FE 1654881114=(1654881114:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 5) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 5) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 5) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 5) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 1365107723) (algebraMap FP FE 1782692429) (algebraMap FP FE 1654881114)
    (Port5Q1_OpeningValues.values (JFn_Values.value 5))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 5)
      (JFv_TX2_CircleGeometry.inverse err seed 5)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 5 (JFv_TX2_CircleGeometry.inverse err seed 5)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 5 2,
    JFv_TX2_CircleGeometry.decoded err seed 5 3,
    JFv_TX2_CircleGeometry.decoded err seed 5 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 5).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((1935845750<2147483647 ∧ 472381860<2147483647) ∧ (678537224<2147483647 ∧ 236705647<2147483647)) ∧
      ((120292263<2147483647 ∧ 1606675882<2147483647) ∧ (137257660<2147483647 ∧ 247347224<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q5_Line
end
