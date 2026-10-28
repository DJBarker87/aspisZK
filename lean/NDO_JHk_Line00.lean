import NDO_JGw_Line0
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line00
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 0
def v0 : FE := ⟨⟨⟨1320773618,1877397073⟩,⟨1270151964,305062365⟩⟩,⟨⟨1020420403,915035097⟩,⟨599194724,1817990359⟩⟩⟩
def v1 : FE := ⟨⟨⟨1563861204,1072163658⟩,⟨411747604,1798218478⟩⟩,⟨⟨1109478725,1870686468⟩,⟨771145124,708078029⟩⟩⟩
def v2 : FE := ⟨⟨⟨1021480397,229375840⟩,⟨1188872916,1965336302⟩⟩,⟨⟨1059617637,452497105⟩,⟨253464645,987991798⟩⟩⟩
def v3 : FE := ⟨⟨⟨95730862,1359327733⟩,⟨1229841427,1475802313⟩⟩,⟨⟨1309751629,1193187707⟩,⟨670744641,1839779700⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1910782771,1386833017⟩,⟨2006240812,241643930⟩⟩,⟨⟨1104440110,1601160972⟩,⟨1411226433,1315189585⟩⟩⟩
def c1 : FE := ⟨⟨⟨1923754017,18429885⟩,⟨911741487,1180365991⟩⟩,⟨⟨1569840694,1492990121⟩,⟨2122865781,500078745⟩⟩⟩
def h0 : FE := ⟨⟨⟨1537332432,1134566076⟩,⟨488282566,312363041⟩⟩,⟨⟨51075275,1644722506⟩,⟨1647379107,264718148⟩⟩⟩
def h1 : FE := ⟨⟨⟨1917268394,702631451⟩,⟨385249326,1784746784⟩⟩,⟨⟨1337140402,473333723⟩,⟨1767046107,907634165⟩⟩⟩
def h2 : FE := ⟨⟨⟨1808935948,1133014053⟩,⟨1830929036,1040324227⟩⟩,⟨⟨2090483322,178969101⟩,⟨2051761551,1513288923⟩⟩⟩
def h3 : FE := ⟨⟨⟨103088253,480969033⟩,⟨1992982168,396973913⟩⟩,⟨⟨1276342778,943619448⟩,⟨1771933234,1293977349⟩⟩⟩
def t2 : FE := ⟨⟨⟨565991324,253473995⟩,⟨52383165,353794934⟩⟩,⟨⟨742888871,2025291806⟩,⟨1305332274,2076654145⟩⟩⟩
def t1 : FE := ⟨⟨⟨775278911,2012333652⟩,⟨996238689,235795432⟩⟩,⟨⟨1768572794,1325049046⟩,⟨1013166275,1481878276⟩⟩⟩
def value : FE := ⟨⟨⟨693198916,639986381⟩,⟨1864761200,1927747454⟩⟩,⟨⟨2142802787,1648541873⟩,⟨1657099671,1353897268⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(1548088906 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1482930998 1548088906 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(1295780117 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 760627696 1295780117 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(1146383522 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1667939589 1146383522 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*1146383522)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*1548088906)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*1295780117)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*1146383522)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (1548088906:FE) (1295780117:FE) (1146383522:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line0.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values0.value inverse (JGw_Line0.value inverse)
    (JGw_Line0.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map1548088906 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1548088906=(1548088906:FE) := map_natCast _ _
  have map1295780117 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1295780117=(1295780117:FE) := map_natCast _ _
  have map1146383522 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1146383522=(1146383522:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values0.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map1548088906,map1295780117,map1146383522,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line00
end
