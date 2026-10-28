import NDO_JGw_Line3
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line03
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 3
def v0 : FE := ⟨⟨⟨1654760959,1780566121⟩,⟨1145494261,819486776⟩⟩,⟨⟨480012192,1675691627⟩,⟨1336652276,1865860444⟩⟩⟩
def v1 : FE := ⟨⟨⟨1056851884,1665049839⟩,⟨1624045842,1818324685⟩⟩,⟨⟨572854969,186035269⟩,⟨667382904,1556558713⟩⟩⟩
def v2 : FE := ⟨⟨⟨782984098,116858813⟩,⟨1881615806,859035786⟩⟩,⟨⟨951340756,1723451480⟩,⟨399757087,1183503165⟩⟩⟩
def v3 : FE := ⟨⟨⟨1345579330,252607270⟩,⟨2100509967,628802256⟩⟩,⟨⟨245603780,1844768942⟩,⟨1576033504,1382024442⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1634739563,2081053101⟩,⟨516420566,942745758⟩⟩,⟨⟨204580964,288992250⟩,⟨612784659,1621390⟩⟩⟩
def c1 : FE := ⟨⟨⟨1954954447,1623769165⟩,⟨292105275,1240750323⟩⟩,⟨⟨1519042264,1628877531⟩,⟨162618923,1753003351⟩⟩⟩
def h0 : FE := ⟨⟨⟨673173156,416899599⟩,⟨1687916469,494541464⟩⟩,⟨⟨1099323836,283745006⟩,⟨458085531,1496986691⟩⟩⟩
def h1 : FE := ⟨⟨⟨1794847005,1852411133⟩,⟨1478004744,18006217⟩⟩,⟨⟨861811614,2032676714⟩,⟨387701791,1951054194⟩⟩⟩
def h2 : FE := ⟨⟨⟨1306957895,929095323⟩,⟨1109272731,2120489168⟩⟩,⟨⟨1269444007,89519122⟩,⟨1268593539,2082908548⟩⟩⟩
def h3 : FE := ⟨⟨⟨1824050841,436601226⟩,⟨260117034,1156406683⟩⟩,⟨⟨2019262592,1140281150⟩,⟨155505376,432384071⟩⟩⟩
def t2 : FE := ⟨⟨⟨779203787,1137316287⟩,⟨901112575,356726777⟩⟩,⟨⟨1389580145,637519672⟩,⟨840775935,2089974536⟩⟩⟩
def t1 : FE := ⟨⟨⟨294742939,773524537⟩,⟨238458963,719420994⟩⟩,⟨⟨1697641822,2129742351⟩,⟨1564821146,343816497⟩⟩⟩
def value : FE := ⟨⟨⟨1486385033,641769127⟩,⟨268612740,885452757⟩⟩,⟨⟨2147418281,2102404536⟩,⟨1140985490,77746572⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(330006617 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 625207909 330006617 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(967967837 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 2012824250 967967837 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(1648821744 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 145254088 1648821744 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*1648821744)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*330006617)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*967967837)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*1648821744)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (330006617:FE) (967967837:FE) (1648821744:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line3.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values3.value inverse (JGw_Line3.value inverse)
    (JGw_Line3.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map330006617 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 330006617=(330006617:FE) := map_natCast _ _
  have map967967837 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 967967837=(967967837:FE) := map_natCast _ _
  have map1648821744 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1648821744=(1648821744:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values3.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map330006617,map967967837,map1648821744,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line03
end
