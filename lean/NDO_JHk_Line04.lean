import NDO_JGw_Line4
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line04
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 4
def v0 : FE := ⟨⟨⟨671337488,1901021208⟩,⟨497274848,1331167961⟩⟩,⟨⟨1381240697,1835046799⟩,⟨703737261,346517556⟩⟩⟩
def v1 : FE := ⟨⟨⟨1610806253,1950016415⟩,⟨1387353283,1122721168⟩⟩,⟨⟨1778923990,776654507⟩,⟨735539447,2024481296⟩⟩⟩
def v2 : FE := ⟨⟨⟨245097044,604007735⟩,⟨472816414,790316287⟩⟩,⟨⟨814641984,733474112⟩,⟨679597612,815958365⟩⟩⟩
def v3 : FE := ⟨⟨⟨1733495406,1006483110⟩,⟨1825086166,254379937⟩⟩,⟨⟨2096922458,1310138954⟩,⟨1695658189,716103946⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1308688833,679407410⟩,⟨1610597596,1565925518⟩⟩,⟨⟨392169334,488952⟩,⟨520517295,630168844⟩⟩⟩
def c1 : FE := ⟨⟨⟨2009779774,1506003903⟩,⟨860307871,159083295⟩⟩,⟨⟨1434883872,1824851240⟩,⟨24864734,953159594⟩⟩⟩
def h0 : FE := ⟨⟨⟨528313136,1365382117⟩,⟨508761766,1411517250⟩⟩,⟨⟨2054803194,1163828593⟩,⟨1490504039,438894379⟩⟩⟩
def h1 : FE := ⟨⟨⟨585492480,18963833⟩,⟨161710910,1936246230⟩⟩,⟨⟨913526603,912670096⟩,⟨1346432838,791664219⟩⟩⟩
def h2 : FE := ⟨⟨⟨842067531,1292972227⟩,⟨313848296,1283423621⟩⟩,⟨⟨1167238723,61914254⟩,⟨768811379,1434648105⟩⟩⟩
def h3 : FE := ⟨⟨⟨1984331383,418211336⟩,⟨768628973,1984829788⟩⟩,⟨⟨1533787470,1216037670⟩,⟨561074754,224237246⟩⟩⟩
def t2 : FE := ⟨⟨⟨1273702723,543813014⟩,⟨797099437,2001488896⟩⟩,⟨⟨277498753,359179313⟩,⟨359841653,364811461⟩⟩⟩
def t1 : FE := ⟨⟨⟨493895612,281804838⟩,⟨1296999549,1249512482⟩⟩,⟨⟨2010424285,318033961⟩,⟨2051606854,802220365⟩⟩⟩
def value : FE := ⟨⟨⟨1756724545,1716894538⟩,⟨747245482,1119058880⟩⟩,⟨⟨342240434,2099954053⟩,⟨1915563436,734053244⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(1525145926 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1992543287 1525145926 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(684033816 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1212737515 684033816 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(1991042867 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1103609776 1991042867 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*1991042867)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*1525145926)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*684033816)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*1991042867)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (1525145926:FE) (684033816:FE) (1991042867:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line4.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values4.value inverse (JGw_Line4.value inverse)
    (JGw_Line4.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map1525145926 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1525145926=(1525145926:FE) := map_natCast _ _
  have map684033816 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 684033816=(684033816:FE) := map_natCast _ _
  have map1991042867 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1991042867=(1991042867:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values4.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map1525145926,map684033816,map1991042867,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line04
end
