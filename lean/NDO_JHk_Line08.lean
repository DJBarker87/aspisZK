import NDO_JGw_Line8
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line08
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 8
def v0 : FE := ⟨⟨⟨664030414,274126781⟩,⟨590864128,719124115⟩⟩,⟨⟨1728643651,48422914⟩,⟨883504869,1901254830⟩⟩⟩
def v1 : FE := ⟨⟨⟨769210404,57844669⟩,⟨1216294227,947911936⟩⟩,⟨⟨1314863630,516026130⟩,⟨1593396871,1484342503⟩⟩⟩
def v2 : FE := ⟨⟨⟨191870746,398001530⟩,⟨1107537619,699826812⟩⟩,⟨⟨1058797636,422078492⟩,⟨1230196429,1600095536⟩⟩⟩
def v3 : FE := ⟨⟨⟨1375473218,315401171⟩,⟨2100493293,1209606237⟩⟩,⟨⟨161341447,200761296⟩,⟨1539652433,521665819⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨60434024,625929254⟩,⟨1948901451,201434838⟩⟩,⟨⟨913876748,1410373543⟩,⟨1879807572,1127335853⟩⟩⟩
def c1 : FE := ⟨⟨⟨145473116,2070792421⟩,⟨615780047,1035329752⟩⟩,⟨⟨432890196,1530657227⟩,⟨1504978015,1139414651⟩⟩⟩
def h0 : FE := ⟨⟨⟨1823888019,1871956273⟩,⟨716926405,894117275⟩⟩,⟨⟨1065911591,296822208⟩,⟨237945827,1376839672⟩⟩⟩
def h1 : FE := ⟨⟨⟨102953570,274619014⟩,⟨1282340749,618382295⟩⟩,⟨⟨673383472,1470515385⟩,⟨618650970,1133375252⟩⟩⟩
def h2 : FE := ⟨⟨⟨196615704,57447193⟩,⟨1854131047,779071520⟩⟩,⟨⟨674026848,717418954⟩,⟨224059584,1901036429⟩⟩⟩
def h3 : FE := ⟨⟨⟨1494413431,1462350241⟩,⟨1981114694,39402603⟩⟩,⟨⟨153850268,708337339⟩,⟨52715321,288688384⟩⟩⟩
def t2 : FE := ⟨⟨⟨928856510,1484827810⟩,⟨770274854,1306283456⟩⟩,⟨⟨1931696294,79784668⟩,⟨966842931,411569860⟩⟩⟩
def t1 : FE := ⟨⟨⟨1101195755,2015110516⟩,⟨536505021,69304003⟩⟩,⟨⟨1961544924,277742908⟩,⟨411831325,1847200792⟩⟩⟩
def value : FE := ⟨⟨⟨313131969,1815705108⟩,⟨150686342,1526262263⟩⟩,⟨⟨610612430,571614974⟩,⟨1765356495,1775372326⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(1750641248 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1696264123 1750641248 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(570515005 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1866831693 570515005 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(1814359028 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1622045998 1814359028 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*1814359028)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*1750641248)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*570515005)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*1814359028)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (1750641248:FE) (570515005:FE) (1814359028:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line8.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values8.value inverse (JGw_Line8.value inverse)
    (JGw_Line8.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map1750641248 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1750641248=(1750641248:FE) := map_natCast _ _
  have map570515005 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 570515005=(570515005:FE) := map_natCast _ _
  have map1814359028 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1814359028=(1814359028:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values8.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map1750641248,map570515005,map1814359028,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line08
end
