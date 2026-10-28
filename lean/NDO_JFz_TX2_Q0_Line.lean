import NDO_JFn_Lines
import NDO_JFw_TX2_CircleNumbers
import NDO_JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q0_Line
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
def alpha : FE := ⟨⟨⟨1923325677,606708475⟩,⟨390399940,1424274113⟩⟩,⟨⟨1600018693,561365806⟩,⟨1230057896,509172918⟩⟩⟩
def d0 : FE := ⟨⟨⟨1495862191,567078347⟩,⟨822330498,1320403121⟩⟩,⟨⟨1444941663,1346309889⟩,⟨1049237274,875315436⟩⟩⟩
def d1 : FE := ⟨⟨⟨113909661,89704391⟩,⟨795026575,2113142288⟩⟩,⟨⟨1284560133,623893483⟩,⟨795489078,1526441663⟩⟩⟩
def d2 : FE := ⟨⟨⟨71556150,2132269355⟩,⟨1374888388,1054874463⟩⟩,⟨⟨191642238,66970454⟩,⟨548253468,610343033⟩⟩⟩
def d3 : FE := ⟨⟨⟨2028222263,814288248⟩,⟨354118641,1376248873⟩⟩,⟨⟨1642244954,2101120408⟩,⟨22065465,1602413776⟩⟩⟩
def c0 : FE := ⟨⟨⟨2084804601,1778643344⟩,⟨974264204,193506010⟩⟩,⟨⟨373464867,422691406⟩,⟨1146286705,2041254811⟩⟩⟩
def c1 : FE := ⟨⟨⟨1072233214,2070334085⟩,⟨1975066861,783206668⟩⟩,⟨⟨1008397953,674624573⟩,⟨218916694,1037950142⟩⟩⟩
def h0 : FE := ⟨⟨⟨1464258478,1437705997⟩,⟨1910332849,2003038098⟩⟩,⟨⟨1140847247,2108315382⟩,⟨1140632233,1153628477⟩⟩⟩
def h1 : FE := ⟨⟨⟨504777084,850746891⟩,⟨400923709,488356339⟩⟩,⟨⟨690931410,1622399813⟩,⟨1756343523,465860653⟩⟩⟩
def h2 : FE := ⟨⟨⟨1294924134,186186907⟩,⟨1419340749,255040158⟩⟩,⟨⟨303375532,603901194⟩,⟨1554624304,1929597017⟩⟩⟩
def h3 : FE := ⟨⟨⟨333495318,2053493018⟩,⟨2068242925,1366123395⟩⟩,⟨⟨2117851484,2087700724⟩,⟨346934755,735916749⟩⟩⟩
def t2 : FE := ⟨⟨⟨970905884,1255794035⟩,⟨755772200,1250942155⟩⟩,⟨⟨453753606,1098806894⟩,⟨831135708,251856953⟩⟩⟩
def t1 : FE := ⟨⟨⟨50431242,2082941577⟩,⟨128987537,1888460103⟩⟩,⟨⟨1587367454,898673613⟩,⟨1334807740,165235379⟩⟩⟩
def answer : FE := ⟨⟨⟨293041818,940239649⟩,⟨1369505055,1718905650⟩⟩,⟨⟨1370376510,1155774066⟩,⟨310016233,831259137⟩⟩⟩
def value : SAQ_WideABI.E := FIo_Install.fromE ⟨⟨⟨293041818#u32,940239649#u32⟩,⟨1369505055#u32,1718905650#u32⟩⟩,⟨⟨1370376510#u32,1155774066#u32⟩,⟨310016233#u32,831259137#u32⟩⟩⟩
theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
theorem c0_eq : (d0-d1)*(1073741824*2137944834)=c0 := by
  unfold d0 d1 c0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c0_eq
theorem c1_eq : (d3-d2)*(1073741824*593156705)=c1 := by
  unfold d3 d2 c1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms c1_eq
theorem h0_eq : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h0_eq
theorem h2_eq : (d0+d1-d2-d3)*(536870912*1740190360)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h2_eq
theorem h1_eq : (c0+c1)*1073741824=h1 := by
  unfold c0 c1 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms h1_eq
theorem h3_eq : (c0-c1)*(1073741824*1740190360)=h3 := by
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
theorem inv0 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 0).lineX)⁻¹=(2137944834:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 655255154 2137944834 (by norm_num)
theorem cast0 : algebraMap FP FE 2137944834=(2137944834:FE) := map_natCast _ _
#print axioms inv0
#print axioms cast0
theorem inv1 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 0).lineY)⁻¹=(593156705:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 340889949 593156705 (by norm_num)
theorem cast1 : algebraMap FP FE 593156705=(593156705:FE) := map_natCast _ _
#print axioms inv1
#print axioms cast1
theorem inv2 : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 0).lineZ)⁻¹=(1740190360:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal 1254335903 1740190360 (by norm_num)
theorem cast2 : algebraMap FP FE 1740190360=(1740190360:FE) := map_natCast _ _
#print axioms inv2
#print axioms cast2
theorem v0 : Port5Q1_OpeningValues.values (JFn_Values.value 0) 0=d0 := rfl
#print axioms v0
theorem v1 : Port5Q1_OpeningValues.values (JFn_Values.value 0) 1=d1 := rfl
#print axioms v1
theorem v2 : Port5Q1_OpeningValues.values (JFn_Values.value 0) 2=d2 := rfl
#print axioms v2
theorem v3 : Port5Q1_OpeningValues.values (JFn_Values.value 0) 3=d3 := rfl
#print axioms v3
theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE 2137944834) (algebraMap FP FE 593156705) (algebraMap FP FE 1740190360)
    (Port5Q1_OpeningValues.values (JFn_Values.value 0))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  simp only [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq]
  rw [horner2,horner1,horner0]

theorem source {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value 0)
      (JFv_TX2_CircleGeometry.inverse err seed 0)=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source 0 (JFv_TX2_CircleGeometry.inverse err seed 0)
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed 0 2,
    JFv_TX2_CircleGeometry.decoded err seed 0 3,
    JFv_TX2_CircleGeometry.decoded err seed 0 4] at sem
  change CheckpointBytes5Output.ofE out=FoldRuntimeAlgebra.lineWithInverses _
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 0).lineX)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 0).lineY)⁻¹)
    (algebraMap FP FE (S7JoinBasisMachine.decode (JFv_TX2_Rows.value 0).lineZ)⁻¹) _ at sem
  rw [inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change ((293041818<2147483647 ∧ 940239649<2147483647) ∧ (1369505055<2147483647 ∧ 1718905650<2147483647)) ∧
      ((1370376510<2147483647 ∧ 1155774066<2147483647) ∧ (310016233<2147483647 ∧ 831259137<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.JFz_TX2_Q0_Line
end
