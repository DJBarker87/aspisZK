import NDO_JGw_Line9
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line09
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 9
def v0 : FE := ⟨⟨⟨594231039,1768961454⟩,⟨1584022688,262305210⟩⟩,⟨⟨1497600569,1037168300⟩,⟨1395967439,1039079598⟩⟩⟩
def v1 : FE := ⟨⟨⟨1504351165,389464337⟩,⟨1673641914,919002449⟩⟩,⟨⟨1955910997,794125224⟩,⟨328630422,135755893⟩⟩⟩
def v2 : FE := ⟨⟨⟨36575841,362686844⟩,⟨1584107066,844875834⟩⟩,⟨⟨2070399795,1671459129⟩,⟨1732952581,291883057⟩⟩⟩
def v3 : FE := ⟨⟨⟨37725191,1856947094⟩,⟨1016008733,1707136693⟩⟩,⟨⟨1962004440,1786102911⟩,⟨528433090,327217950⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1998935804,1761158592⟩,⟨2009200790,1500215158⟩⟩,⟨⟨1438727239,397104649⟩,⟨929882515,1886053654⟩⟩⟩
def c1 : FE := ⟨⟨⟨1609086529,434735744⟩,⟨297409697,979762671⟩⟩,⟨⟨1585374510,1713793627⟩,⟨1585767117,2045666021⟩⟩⟩
def h0 : FE := ⟨⟨⟨543220809,1631385844⟩,⟨2001316012,2007071870⟩⟩,⟨⟨260866215,1322213891⟩,⟨996495883,1522225948⟩⟩⟩
def h1 : FE := ⟨⟨⟨730269343,1097947168⟩,⟨79563420,166247091⟩⟩,⟨⟨438309051,1055449138⟩,⟨1257824816,892118014⟩⟩⟩
def h2 : FE := ⟨⟨⟨434243242,1558241725⟩,⟨1977986427,1598036496⟩⟩,⟨⟨713359992,1808577011⟩,⟨122873800,1535361666⟩⟩⟩
def h3 : FE := ⟨⟨⟨1573324342,812554257⟩,⟨1571652835,1551451967⟩⟩,⟨⟨1004359070,89972337⟩,⟨404724682,570571975⟩⟩⟩
def t2 : FE := ⟨⟨⟨989039671,667357280⟩,⟨1486233465,893365504⟩⟩,⟨⟨963927033,1058898952⟩,⟨530398712,1077092142⟩⟩⟩
def t1 : FE := ⟨⟨⟨1766596244,1405451977⟩,⟨2124717576,1498437037⟩⟩,⟨⟨1088556649,1574170262⟩,⟨1301275078,1241272483⟩⟩⟩
def value : FE := ⟨⟨⟨795046778,1374188295⟩,⟨460169651,568293753⟩⟩,⟨⟨1033592440,750200039⟩,⟨1739915931,1242973730⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(441414646 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1156763297 441414646 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(62195466 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1907806345 62195466 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(1272511770 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 2023658180 1272511770 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*1272511770)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*441414646)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*62195466)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*1272511770)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (441414646:FE) (62195466:FE) (1272511770:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line9.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values9.value inverse (JGw_Line9.value inverse)
    (JGw_Line9.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map441414646 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 441414646=(441414646:FE) := map_natCast _ _
  have map62195466 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 62195466=(62195466:FE) := map_natCast _ _
  have map1272511770 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1272511770=(1272511770:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values9.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map441414646,map62195466,map1272511770,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line09
end
