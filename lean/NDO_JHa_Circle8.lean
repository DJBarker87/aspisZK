import NDO_JGr_Geometry
import NDO_JFw_TX2_CircleNumbers
import NDO_JHa_Dots8
import NDO_JGw_Circle8
import NDO_JGw_Values8
import NDO_JFv_TX2_Query0Inverse
import NDO_JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle8
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value08_1.value
def d0 : FE := ⟨⟨⟨785136080,1119168087⟩,⟨828182209,255954801⟩⟩,⟨⟨576478090,1008883790⟩,⟨2109828463,346997716⟩⟩⟩
def h0 : FE := ⟨⟨⟨265947147,1393717366⟩,⟨296248963,439808917⟩⟩,⟨⟨368216265,1808092910⟩,⟨900535677,1836524762⟩⟩⟩
def d1 : FE := ⟨⟨⟨346389291,822587058⟩,⟨1654116951,451444269⟩⟩,⟨⟨919675880,250077772⟩,⟨1308804866,1040159619⟩⟩⟩
def h1 : FE := ⟨⟨⟨1086641977,1101833591⟩,⟨251853222,1500954145⟩⟩,⟨⟨671835256,1308915539⟩,⟨1505838681,458636885⟩⟩⟩
def d2 : FE := ⟨⟨⟨1654106065,918901178⟩,⟨146561791,415977228⟩⟩,⟨⟨1966525320,140857527⟩,⟨1839272516,1866181757⟩⟩⟩
def h2 : FE := ⟨⟨⟨1840533502,578224648⟩,⟨1697457370,57761582⟩⟩,⟨⟨1934870413,1335612799⟩,⟨1637145889,985445503⟩⟩⟩
def d3 : FE := ⟨⟨⟨425640799,566729494⟩,⟨703618548,635859370⟩⟩,⟨⟨157669417,1537585257⟩,⟨491720510,1945276309⟩⟩⟩
def h3 : FE := ⟨⟨⟨194306779,1043061695⟩,⟨1847667786,1706721433⟩⟩,⟨⟨1182499801,947870585⟩,⟨433369834,1136780690⟩⟩⟩
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def t2 : FE := ⟨⟨⟨12474583,1368682884⟩,⟨358655258,1600256510⟩⟩,⟨⟨270516251,1549682085⟩,⟨332859057,625717771⟩⟩⟩
def t1 : FE := ⟨⟨⟨346561195,953649155⟩,⟨833474037,22744759⟩⟩,⟨⟨1560351970,1909581608⟩,⟨486944372,796687085⟩⟩⟩
def value : FE := ⟨⟨⟨769210404,57844669⟩,⟨1216294227,947911936⟩⟩,⟨⟨1314863630,516026130⟩,⟨1593396871,1484342503⟩⟩⟩
theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value 8).x)⁻¹=(2093273847 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 716392373 2093273847 (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value 8).y)⁻¹=(1009991687 : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal 1087788265 1009991687 (by norm_num)
#print axioms invX
#print axioms invY
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  unfold d0 d1 d2 d3 h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient0
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1009991687)=h1 := by
  unfold d0 d1 d2 d3 h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient1
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*2093273847)=h2 := by
  unfold d0 d1 d2 d3 h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms coefficient2
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*2093273847*1009991687)=h3 := by
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
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2093273847)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1009991687)
    (Port5Q1_OpeningValues.values JHa_Dots8.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 2093273847=(2093273847:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1009991687=(1009991687:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots8.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots8.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots8.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots8.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots8.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry 8)=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle8.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots8.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change ((769210404<2147483647 ∧ 57844669<2147483647) ∧ (1216294227<2147483647 ∧ 947911936<2147483647)) ∧
      ((1314863630<2147483647 ∧ 516026130<2147483647) ∧ (1593396871<2147483647 ∧ 1484342503<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle8
end
