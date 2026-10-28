import NDO_JGw_Line7
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line07
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 7
def v0 : FE := ⟨⟨⟨1455069336,44819172⟩,⟨1218322180,1351758312⟩⟩,⟨⟨178743778,243044163⟩,⟨1790351735,1889787775⟩⟩⟩
def v1 : FE := ⟨⟨⟨600865669,1760543780⟩,⟨1643193913,1050852917⟩⟩,⟨⟨1700349525,550772394⟩,⟨529185211,326904698⟩⟩⟩
def v2 : FE := ⟨⟨⟨1656677859,519419504⟩,⟨1794599757,820488980⟩⟩,⟨⟨1435165728,666249457⟩,⟨421867039,613764257⟩⟩⟩
def v3 : FE := ⟨⟨⟨1624881175,334229555⟩,⟨1231804413,2095236360⟩⟩,⟨⟨394298181,127601937⟩,⟨180333677,1814595571⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨953627377,1410627638⟩,⟨1996951634,344833067⟩⟩,⟨⟨199436352,636120705⟩,⟨466316804,1881464500⟩⟩⟩
def c1 : FE := ⟨⟨⟨275614862,1574791835⟩,⟨674350427,707021452⟩⟩,⟨⟨178958080,464180062⟩,⟨1216560847,442845470⟩⟩⟩
def h0 : FE := ⟨⟨⟨797502598,127882091⟩,⟨935109154,1866455054⟩⟩,⟨⟨927139303,2007529723⟩,⟨1804176239,1698133987⟩⟩⟩
def h1 : FE := ⟨⟨⟨1688362943,418967913⟩,⟨261909207,1599669083⟩⟩,⟨⟨189197216,1623892207⟩,⟨1915180649,1162154985⟩⟩⟩
def h2 : FE := ⟨⟨⟨1704678216,1311080484⟩,⟨1608118525,1716237088⟩⟩,⟨⟨745692587,1321021384⟩,⟨1075517975,493263962⟩⟩⟩
def h3 : FE := ⟨⟨⟨1527330055,1114220658⟩,⟨486729254,1361828785⟩⟩,⟨⟨90223943,2036979196⟩,⟨14989372,1774228152⟩⟩⟩
def t2 : FE := ⟨⟨⟨445678176,44409634⟩,⟨1364305730,1704542919⟩⟩,⟨⟨942696830,1248548612⟩,⟨1341391468,221961597⟩⟩⟩
def t1 : FE := ⟨⟨⟨1605096046,1422744071⟩,⟨615700043,274370504⟩⟩,⟨⟨729557498,951106009⟩,⟨440702275,1057033681⟩⟩⟩
def value : FE := ⟨⟨⟨321305315,1142875242⟩,⟨10932055,432158760⟩⟩,⟨⟨140563111,1928915987⟩,⟨245305444,1453663545⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(2025905732 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1653909379 2025905732 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(896940220 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1091258478 896940220 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(731066594 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1778447451 731066594 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*731066594)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*2025905732)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*896940220)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*731066594)=h3 := by
  unfold c0 c1 h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef3
theorem horner2 : h2+alpha*h3=t2 := by
  unfold alpha h2 h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner2
theorem horner1 : h1+alpha*t2=t1 := by
  unfold alpha h1 t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner1
theorem horner0 : h0+alpha*t1=value := by
  unfold alpha h0 t1 value
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner0
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (2025905732:FE) (896940220:FE) (731066594:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line7.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values7.value inverse (JGw_Line7.value inverse)
    (JGw_Line7.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map2025905732 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2025905732=(2025905732:FE) := map_natCast _ _
  have map896940220 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 896940220=(896940220:FE) := map_natCast _ _
  have map731066594 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 731066594=(731066594:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values7.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map2025905732,map896940220,map731066594,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line07
end
