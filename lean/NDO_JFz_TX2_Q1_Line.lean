import NDO_JFn_Lines
import NDO_JFw_TX2_CircleNumbers
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨939634098,31431390⟩,⟨696747450,309953685⟩⟩,⟨⟨1224205441,619654007⟩,⟨1209377263,1914339141⟩⟩⟩
def d1 : FE := ⟨⟨⟨2096783160,973349216⟩,⟨58875228,883428442⟩⟩,⟨⟨1992183950,1411562134⟩,⟨1199675175,925513126⟩⟩⟩
def d2 : FE := ⟨⟨⟨12674944,1246410058⟩,⟨116774269,918536601⟩⟩,⟨⟨1000197073,68609528⟩,⟨19935596,1874953030⟩⟩⟩
def d3 : FE := ⟨⟨⟨2113538273,472258602⟩,⟨1891916025,1511907743⟩⟩,⟨⟨300398393,1245637887⟩,⟨1073497836,2094029351⟩⟩⟩
def c0 : FE := ⟨⟨⟨2140093308,324204721⟩,⟨1569458927,528906044⟩⟩,⟨⟨1157584398,1518640469⟩,⟨675335208,469605397⟩⟩⟩
def c1 : FE := ⟨⟨⟨1771614297,1446036693⟩,⟨352137652,705503762⟩⟩,⟨⟨1452311025,2122987237⟩,⟨2078463790,1887151982⟩⟩⟩
def h0 : FE := ⟨⟨⟨753786707,1754604140⟩,⟨691078243,369085706⟩⟩,⟨⟨1666117126,836365889⟩,⟨1949363291,1702208662⟩⟩⟩
def h1 : FE := ⟨⟨⟨882111979,885120707⟩,⟨2034540113,617204903⟩⟩,⟨⟨231205888,1820813853⟩,⟨1376899499,104636866⟩⟩⟩
def h2 : FE := ⟨⟨⟨32316302,386133573⟩,⟨1742596770,349762950⟩⟩,⟨⟨1386456209,20940776⟩,⟨404877304,1703898825⟩⟩⟩
def h3 : FE := ⟨⟨⟨60296870,2067447826⟩,⟨26384689,1789802890⟩⟩,⟨⟨1873548812,1947868031⟩,⟨613132049,1627490988⟩⟩⟩
def t2 : FE := ⟨⟨⟨442818480,1964145103⟩,⟨477527214,121709538⟩⟩,⟨⟨173358915,569320143⟩,⟨1475489064,511497857⟩⟩⟩
def t1 : FE := ⟨⟨⟨1486669907,1930310820⟩,⟨675768077,40669081⟩⟩,⟨⟨116619673,1252900671⟩,⟨1715689972,395962320⟩⟩⟩
def answer : FE := ⟨⟨⟨327334623,680146744⟩,⟨962621904,340908788⟩⟩,⟨⟨1911803263,259864830⟩,⟨177247337,1873129611⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨327334623#u32,680146744#u32⟩,⟨962621904#u32,340908788#u32⟩⟩,⟨⟨1911803263#u32,259864830#u32⟩,⟨177247337#u32,1873129611#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*210433035)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*1645965264)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1373457310)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1373457310)=h3 := by
  unfold c0 c1 h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h3_eq
theorem horner2 : h2+alpha*h3=t2 := by
  unfold h2 alpha h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner2
theorem horner1 : h1+alpha*t2=t1 := by
  unfold h1 alpha t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner1
theorem horner0 : h0+alpha*t1=answer := by
  unfold h0 alpha t1 answer
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner0
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).lineX)⁻¹=(210433035:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 397483683 210433035 (by norm_num)
theorem cast0 : algebraMap FP FE 210433035=(210433035:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).lineY)⁻¹=(1645965264:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1376692134 1645965264 (by norm_num)
theorem cast1 : algebraMap FP FE 1645965264=(1645965264:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).lineZ)⁻¹=(1373457310:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1592160195 1373457310 (by norm_num)
theorem cast2 : algebraMap FP FE 1373457310=(1373457310:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 1) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 1) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 1) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 1) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 210433035) (algebraMap FP FE 1645965264) (algebraMap FP FE 1373457310)
    (Port5Q1_OpeningValues.values (JFn_Values.value 1))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 1)
      (JFv_TX2_CircleGeometry.inverse err seed 1)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 1 (JFv_TX2_CircleGeometry.inverse err seed 1)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 1 2,
    JFv_TX2_CircleGeometry.decoded err seed 1 3,
    JFv_TX2_CircleGeometry.decoded err seed 1 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 1).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((327334623<2147483647 ∧ 680146744<2147483647) ∧ (962621904<2147483647 ∧ 340908788<2147483647)) ∧
      ((1911803263<2147483647 ∧ 259864830<2147483647) ∧ (177247337<2147483647 ∧ 1873129611<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q1_Line
end
