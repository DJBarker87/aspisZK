import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots0
import NDO_JGw_Circle0
import NDO_JGw_Values0
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle0
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value00_3.value
def d0 : FE := ⟨⟨⟨104132695,1651415809⟩,⟨507121032,221042496⟩⟩,⟨⟨1130441,1178487768⟩,⟨154802184,64723860⟩⟩⟩
def h0 : FE := ⟨⟨⟨487981623,824562094⟩,⟨111298212,1851773764⟩⟩,⟨⟨1631724340,679883371⟩,⟨1263356948,93332514⟩⟩⟩
def d1 : FE := ⟨⟨⟨2045764542,548531564⟩,⟨1467598750,257544154⟩⟩,⟨⟨1102161475,1010421797⟩,⟨620633619,947414456⟩⟩⟩
def h1 : FE := ⟨⟨⟨1936278973,231141685⟩,⟨1120269253,1710718975⟩⟩,⟨⟨1739572031,1325755098⟩,⟨2109173978,750770713⟩⟩⟩
def d2 : FE := ⟨⟨⟨213701450,1562527507⟩,⟨1451282042,277176222⟩⟩,⟨⟨521945569,1460882455⟩,⟨1293777146,1767770813⟩⟩⟩
def h2 : FE := ⟨⟨⟨1799382664,1136271153⟩,⟨1133321033,1710988026⟩⟩,⟨⟨1317206404,2004839973⟩,⟨304948172,619531300⟩⟩⟩
def d3 : FE := ⟨⟨⟨1735811452,1683257143⟩,⟨1314158318,208881243⟩⟩,⟨⟨606692581,1217225111⟩,⟨836731196,1888388221⟩⟩⟩
def h3 : FE := ⟨⟨⟨1868298056,1260237071⟩,⟨1922110259,574900158⟩⟩,⟨⟨585558171,64174083⟩,⟨1076895256,133072842⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨974726864,1856626653⟩,⟨2023748462,715796405⟩⟩,⟨⟨2014565644,761947904⟩,⟨1445233748,130000695⟩⟩⟩
def t1 : FE := ⟨⟨⟨1743189801,266683019⟩,⟨580676935,257185447⟩⟩,⟨⟨1013326272,720589787⟩,⟨1719703223,25453885⟩⟩⟩
def value : FE := ⟨⟨⟨95730862,1359327733⟩,⟨1229841427,1475802313⟩⟩,⟨⟨1309751629,1193187707⟩,⟨670744641,1839779700⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 0).x)⁻¹=(445523722 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 4199594 445523722 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 0).y)⁻¹=(549654025 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 98204382 549654025 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*549654025)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*445523722)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*445523722*549654025)=h3 := by
  unfold d0 d1 d2 d3 h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient3
theorem horner2 : h2+alpha*h3=t2 := by
  unfold h2 alpha h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner2
theorem horner1 : h1+alpha*t2=t1 := by
  unfold h1 alpha t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner1
theorem horner0 : h0+alpha*t1=value := by
  unfold h0 alpha t1 value
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms horner0
theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 445523722)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 549654025)
    (Port5Q1_OpeningValues.values JHa_Dots0.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 445523722=(445523722:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 549654025=(549654025:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots0.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots0.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots0.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots0.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots0.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 0)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle0.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots0.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((95730862<2147483647 ∧ 1359327733<2147483647) ∧ (1229841427<2147483647 ∧ 1475802313<2147483647)) ∧
      ((1309751629<2147483647 ∧ 1193187707<2147483647) ∧ (670744641<2147483647 ∧ 1839779700<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle0
end
