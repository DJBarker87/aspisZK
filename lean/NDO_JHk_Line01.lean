import NDO_JGw_Line1
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line01
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 1
def v0 : FE := ⟨⟨⟨1456580399,841726080⟩,⟨979224028,1847754340⟩⟩,⟨⟨1212465351,709231024⟩,⟨279512060,1739500556⟩⟩⟩
def v1 : FE := ⟨⟨⟨3946788,1921141621⟩,⟨1912846855,81146261⟩⟩,⟨⟨944397719,1465743260⟩,⟨691618691,1876781494⟩⟩⟩
def v2 : FE := ⟨⟨⟨1129387613,315607019⟩,⟨1673928397,1452954405⟩⟩,⟨⟨1916289967,1075044692⟩,⟨688894222,1221141249⟩⟩⟩
def v3 : FE := ⟨⟨⟨8292422,1571991281⟩,⟨44036622,293227156⟩⟩,⟨⟨256204945,2020339820⟩,⟨378728118,301896724⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1577228496,1987023164⟩,⟨938043021,1486077609⟩⟩,⟨⟨1667556763,471822455⟩,⟨1821940347,1957496459⟩⟩⟩
def c1 : FE := ⟨⟨⟨1060283230,523354663⟩,⟨1137736778,1027022786⟩⟩,⟨⟨731963589,1330505793⟩,⟨1139164988,2109236004⟩⟩⟩
def h0 : FE := ⟨⟨⟨1723293629,1699487412⟩,⟨78767152,1992512364⟩⟩,⟨⟨8597672,1317589699⟩,⟨2120301008,747959094⟩⟩⟩
def h1 : FE := ⟨⟨⟨1318755863,181447090⟩,⟨2111631723,182808374⟩⟩,⟨⟨1199760176,901164124⟩,⟨406810844,959624408⟩⟩⟩
def h2 : FE := ⟨⟨⟨480247035,1558616219⟩,⟨2135096831,1616626295⟩⟩,⟨⟨2146156917,367752640⟩,⟨1643941565,1234227655⟩⟩⟩
def h3 : FE := ⟨⟨⟨1299686,1758411330⟩,⟨2016947369,1481226758⟩⟩,⟨⟨358549270,1105418103⟩,⟨495093198,1508412397⟩⟩⟩
def t2 : FE := ⟨⟨⟨429518239,1101947627⟩,⟨454542096,1949107574⟩⟩,⟨⟨1580372227,973597018⟩,⟨1308077044,603581737⟩⟩⟩
def t1 : FE := ⟨⟨⟨786156297,894701266⟩,⟨1818676624,763523058⟩⟩,⟨⟨1234510949,1756906163⟩,⟨1815552799,2110744836⟩⟩⟩
def value : FE := ⟨⟨⟨608038418,2035529987⟩,⟨1627580570,1264720253⟩⟩,⟨⟨424887596,1267828159⟩,⟨1951748929,252217331⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(487530179 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1220228973 487530179 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(1062940330 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1792229318 1062940330 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(2090511836 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 2099472686 2090511836 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*2090511836)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*487530179)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*1062940330)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*2090511836)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (487530179:FE) (1062940330:FE) (2090511836:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line1.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values1.value inverse (JGw_Line1.value inverse)
    (JGw_Line1.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map487530179 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 487530179=(487530179:FE) := map_natCast _ _
  have map1062940330 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1062940330=(1062940330:FE) := map_natCast _ _
  have map2090511836 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2090511836=(2090511836:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values1.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map487530179,map1062940330,map2090511836,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line01
end
