import NDO_JGw_Line6
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line06
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 6
def v0 : FE := ⟨⟨⟨494412570,1427631101⟩,⟨5260489,277573310⟩⟩,⟨⟨364466490,400123641⟩,⟨2092986464,176710615⟩⟩⟩
def v1 : FE := ⟨⟨⟨1396410589,253103824⟩,⟨812667064,1952677907⟩⟩,⟨⟨422301239,1782981050⟩,⟨462977955,1206238169⟩⟩⟩
def v2 : FE := ⟨⟨⟨1438858277,100051946⟩,⟨1191364192,1434773302⟩⟩,⟨⟨346749938,600437687⟩,⟨490465501,1967594027⟩⟩⟩
def v3 : FE := ⟨⟨⟨1730837807,842207747⟩,⟨667964143,1938842104⟩⟩,⟨⟨139811795,57078191⟩,⟨1583247013,1380695758⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨839854994,1483560404⟩,⟨2018712837,1033855052⟩⟩,⟨⟨858504963,1919165658⟩,⟨1526370692,1084046811⟩⟩⟩
def c1 : FE := ⟨⟨⟨28598805,1309632987⟩,⟨36043848,1835917041⟩⟩,⟨⟨1467676268,1628073446⟩,⟨1015262596,1774220348⟩⟩⟩
def h0 : FE := ⟨⟨⟨728258899,1729490478⟩,⟨669313972,864095744⟩⟩,⟨⟨1392074189,1247026054⟩,⟨1694290145,1719680554⟩⟩⟩
def h1 : FE := ⟨⟨⟨1507968723,322854872⟩,⟨2101120166,361144223⟩⟩,⟨⟨89348792,1773619552⟩,⟨1270816644,355391756⟩⟩⟩
def h2 : FE := ⟨⟨⟨443814106,1528744877⟩,⟨2079723578,1712461912⟩⟩,⟨⟨1237609610,1662847227⟩,⟨1513590889,729681032⟩⟩⟩
def h3 : FE := ⟨⟨⟨49263704,1096924295⟩,⟨1776532584,1253669904⟩⟩,⟨⟨776947143,249865559⟩,⟨1988585112,1852793130⟩⟩⟩
def t2 : FE := ⟨⟨⟨1090938018,226009879⟩,⟨352267105,2078785333⟩⟩,⟨⟨515610352,1402580742⟩,⟨993144045,26037678⟩⟩⟩
def t1 : FE := ⟨⟨⟨587829642,1526755155⟩,⟨397243486,1108664939⟩⟩,⟨⟨2054272764,1252035968⟩,⟨1079370978,1283760846⟩⟩⟩
def value : FE := ⟨⟨⟨173039117,997531406⟩,⟨1530004149,214770872⟩⟩,⟨⟨693565198,1411725100⟩,⟨145267460,508990992⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(160258160 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 895487338 160258160 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(1797070723 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1345719795 1797070723 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(968769485 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 350979623 968769485 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*968769485)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*160258160)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*1797070723)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*968769485)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (160258160:FE) (1797070723:FE) (968769485:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line6.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values6.value inverse (JGw_Line6.value inverse)
    (JGw_Line6.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map160258160 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 160258160=(160258160:FE) := map_natCast _ _
  have map1797070723 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1797070723=(1797070723:FE) := map_natCast _ _
  have map968769485 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 968769485=(968769485:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values6.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map160258160,map1797070723,map968769485,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line06
end
