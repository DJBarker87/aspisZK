import NDO_JGw_Line5
import NDO_JGw_Inverses
import NDO_JFv_TX2_Query0Inverse
import NDO_JHk_LineConstants
import NDO_JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_Line05
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry 5
def v0 : FE := ⟨⟨⟨2060537896,1418268399⟩,⟨124297972,1643810385⟩⟩,⟨⟨1177585472,785366786⟩,⟨451118307,1920921062⟩⟩⟩
def v1 : FE := ⟨⟨⟨176288459,886246977⟩,⟨2145784843,55600143⟩⟩,⟨⟨962097383,1554768102⟩,⟨1399764748,111971848⟩⟩⟩
def v2 : FE := ⟨⟨⟨175834614,813019672⟩,⟨597567193,934878347⟩⟩,⟨⟨885784028,1067922863⟩,⟨1691122957,1819234992⟩⟩⟩
def v3 : FE := ⟨⟨⟨902812610,1541094360⟩,⟨1607722716,1463071865⟩⟩,⟨⟨1651209600,1859119510⟩,⟨467514766,410267422⟩⟩⟩
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def c0 : FE := ⟨⟨⟨1403761123,1907980014⟩,⟨1087794329,497871351⟩⟩,⟨⟨767866275,2134243366⟩,⟨196139155,989023609⟩⟩⟩
def c1 : FE := ⟨⟨⟨1041423163,1716943745⟩,⟨1685207753,375172432⟩⟩,⟨⟨1070527077,512057552⟩,⟨2108906888,684908159⟩⟩⟩
def h0 : FE := ⟨⟨⟨291997483,1164657352⟩,⟨1118843181,1024340185⟩⟩,⟨⟨632298209,1853665227⟩,⟨2076122018,1065598831⟩⟩⟩
def h1 : FE := ⟨⟨⟨1222592143,738720056⟩,⟨1386501041,1510263715⟩⟩,⟨⟨919196676,1323150459⟩,⟨78781198,836965884⟩⟩⟩
def h2 : FE := ⟨⟨⟨117998398,668183032⟩,⟨1924786137,103261899⟩⟩,⟨⟨1557072593,271204668⟩,⟨474270273,1042280493⟩⟩⟩
def h3 : FE := ⟨⟨⟨159989899,671150083⟩,⟨244200559,721524440⟩⟩,⟨⟨677800901,1027114326⟩,⟨35705162,556794463⟩⟩⟩
def t2 : FE := ⟨⟨⟨1424757926,1350795349⟩,⟨1521944987,634241427⟩⟩,⟨⟨54224502,1676146762⟩,⟨970550263,1200798579⟩⟩⟩
def t1 : FE := ⟨⟨⟨1120156272,660083389⟩,⟨1875509230,1118297118⟩⟩,⟨⟨25542821,2109063206⟩,⟨4713451,320474034⟩⟩⟩
def value : FE := ⟨⟨⟨1564019087,1397113853⟩,⟨945795750,1095455810⟩⟩,⟨⟨1069439448,1241956085⟩,⟨611435966,1657284701⟩⟩⟩
theorem invX : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)=(260941944 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 959175626 260941944 (by norm_num)
#print axioms invX
theorem invY : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)=(18642787 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1036797898 18642787 (by norm_num)
#print axioms invY
theorem invZ : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)=(999946690 : Port5Q1_QueryPorts.FP) := by
  rw [JGw_Inverses.decoded]
  exact JFv_TX2_Query0Inverse.reciprocal 1076933717 999946690 (by norm_num)
#print axioms invZ
theorem coef0 : (v0+v1+v2+v3)*536870912=h0 := by
  unfold v0 v1 v2 v3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef0
theorem coef2 : (v0+v1-v2-v3)*(536870912*999946690)=h2 := by
  unfold v0 v1 v2 v3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef2
theorem diff0 : (v0-v1)*(1073741824*260941944)=c0 := by
  unfold v0 v1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff0
theorem diff1 : (v3-v2)*(1073741824*18642787)=c1 := by
  unfold v2 v3 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms diff1
theorem coef1 : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coef1
theorem coef3 : (c0-c1)*(1073741824*999946690)=h3 := by
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
theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha (260941944:FE) (18642787:FE) (999946690:FE)
    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by
  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl
  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl
  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl
  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]
  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]
#print axioms formula
theorem source : CheckpointBytes5Output.ofE (JGw_Line5.value inverse)=value := by
  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values5.value inverse (JGw_Line5.value inverse)
    (JGw_Line5.returned inverse)).1
  rw [invX,invY,invZ] at h
  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  have map260941944 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 260941944=(260941944:FE) := map_natCast _ _
  have map18642787 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 18642787=(18642787:FE) := map_natCast _ _
  have map999946690 : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 999946690=(999946690:FE) := map_natCast _ _
  have vs : Port5Q1_OpeningValues.values JGw_Values5.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by
    funext j
    fin_cases j <;> rfl
  rw [a,map260941944,map18642787,map999946690,vs,formula] at h
  exact h
#print axioms source
end AspisR1.JHk_Line05
end
