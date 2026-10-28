import NDO_JGw_Line2
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line02
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 2
def v0 : FE := ⟨⟨⟨1033882084,1752908335⟩,⟨1661726728,493637179⟩⟩,⟨⟨1121358450,2062438048⟩,⟨1867820851,453558728⟩⟩⟩
def v1 : FE := ⟨⟨⟨1590511308,1201712515⟩,⟨1174844659,177624340⟩⟩,⟨⟨73257167,1788406020⟩,⟨1896995077,1817016679⟩⟩⟩
def v2 : FE := ⟨⟨⟨1020750806,2008592790⟩,⟨1441332143,1949526172⟩⟩,⟨⟨1093750194,551010874⟩,⟨2041841295,1087379731⟩⟩⟩
def v3 : FE := ⟨⟨⟨2105904998,1610425956⟩,⟨641719873,1829180105⟩⟩,⟨⟨146852901,1495337783⟩,⟨1441999667,1898936014⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1714170621,455781144⟩,⟨1158776487,1959015287⟩⟩,⟨⟨1475038057,1963011772⟩,⟨1483583205,643419947⟩⟩⟩
def c1 : FE := ⟨⟨⟨260457139,935935247⟩,⟨2094547853,745728104⟩⟩,⟨⟨738527216,1602623390⟩,⟨793107469,755614146⟩⟩⟩
def h0 : FE := ⟨⟨⟨1437762299,1643409899⟩,⟨693034939,1112491949⟩⟩,⟨⟨608804678,2011169093⟩,⟨738422399,1314222788⟩⟩⟩
def h1 : FE := ⟨⟨⟨987313880,1769600019⟩,⟨1626662170,278629872⟩⟩,⟨⟨33040813,1782817581⟩,⟨1138345337,1773258870⟩⟩⟩
def h2 : FE := ⟨⟨⟨770746568,794522381⟩,⟨28844759,1616065807⟩⟩,⟨⟨2145379855,796181830⟩,⟨16711243,171770838⟩⟩⟩
def h3 : FE := ⟨⟨⟨629100394,1707217780⟩,⟨1038875300,1291736278⟩⟩,⟨⟨1890076050,772882767⟩,⟨1767090963,1913618160⟩⟩⟩
def t2 : FE := ⟨⟨⟨630401710,353731117⟩,⟨311589095,413774542⟩⟩,⟨⟨49272557,354214585⟩,⟨532066911,2036183815⟩⟩⟩
def t1 : FE := ⟨⟨⟨641628174,1194415851⟩,⟨822234158,910535812⟩⟩,⟨⟨300761819,218942617⟩,⟨1560258634,714923797⟩⟩⟩
def value : FE := ⟨⟨⟨668638683,1399516972⟩,⟨200659360,1745853467⟩⟩,⟨⟨1247716643,559966262⟩,⟨376459622,998644509⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(1644389307 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 203043952 1644389307 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(91221686 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1661922674 91221686 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(808957979 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1699037283 808957979 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*808957979)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*1644389307)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*91221686)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*808957979)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (1644389307:FE) (91221686:FE) (808957979:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line2.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values2.value inverse (JGw_Line2.value inverse)
    (JGw_Line2.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map1644389307 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1644389307=(1644389307:FE) := map_natCast _ _
  have map91221686 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 91221686=(91221686:FE) := map_natCast _ _
  have map808957979 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 808957979=(808957979:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values2.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map1644389307,map91221686,map808957979,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line02
end
