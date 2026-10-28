import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots5
import NDO_JGw_Circle5
import NDO_JGw_Values5
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle5
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value05_1.value
def d0 : FE := ⟨⟨⟨889701891,1831850509⟩,⟨1984792026,1468090803⟩⟩,⟨⟨831003424,582650226⟩,⟨630659388,468889793⟩⟩⟩
def h0 : FE := ⟨⟨⟨163103171,581803008⟩,⟨988417684,352923079⟩⟩,⟨⟨963442779,699700553⟩,⟨479620427,1384706537⟩⟩⟩
def d1 : FE := ⟨⟨⟨1782986818,634368823⟩,⟨1026224551,13815773⟩⟩,⟨⟨825477512,608692736⟩,⟨1664668134,1312633504⟩⟩⟩
def h1 : FE := ⟨⟨⟨131371113,1390495803⟩,⟨1296511874,179609023⟩⟩,⟨⟨219431558,732341596⟩,⟨1499696396,92659968⟩⟩⟩
def d2 : FE := ⟨⟨⟨1671330790,242136476⟩,⟨481917149,1289523696⟩⟩,⟨⟨1583721934,134400336⟩,⟨744502957,1192325426⟩⟩⟩
def h2 : FE := ⟨⟨⟨1851563483,1773973049⟩,⟨706005458,1118178881⟩⟩,⟨⟨1048161619,467577596⟩,⟨18294423,709785996⟩⟩⟩
def d3 : FE := ⟨⟨⟨603360479,1766339871⟩,⟨460737010,787745691⟩⟩,⟨⟨613568246,1473058914⟩,⟨1026134876,417493778⟩⟩⟩
def h3 : FE := ⟨⟨⟨1054977677,637793616⟩,⟨745248621,2081952947⟩⟩,⟨⟨1452229838,2032105305⟩,⟨1528826988,2073596320⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨797468644,1457608148⟩,⟨295102175,833184522⟩⟩,⟨⟨35690826,1881903351⟩,⟨695487093,1917998768⟩⟩⟩
def t1 : FE := ⟨⟨⟨1570841481,565842292⟩,⟨817610440,2038345142⟩⟩,⟨⟨1909479209,43873109⟩,⟨1195366817,1639919121⟩⟩⟩
def value : FE := ⟨⟨⟨176288459,886246977⟩,⟨2145784843,55600143⟩⟩,⟨⟨962097383,1554768102⟩,⟨1399764748,111971848⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 5).x)⁻¹=(1884091505 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 170513503 1884091505 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 5).y)⁻¹=(1925169165 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1893994276 1925169165 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1925169165)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*1884091505)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*1884091505*1925169165)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1884091505)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1925169165)
    (Port5Q1_OpeningValues.values JHa_Dots5.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1884091505=(1884091505:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1925169165=(1925169165:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots5.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots5.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots5.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots5.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots5.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 5)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle5.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots5.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((176288459<2147483647 ∧ 886246977<2147483647) ∧ (2145784843<2147483647 ∧ 55600143<2147483647)) ∧
      ((962097383<2147483647 ∧ 1554768102<2147483647) ∧ (1399764748<2147483647 ∧ 111971848<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle5
end
