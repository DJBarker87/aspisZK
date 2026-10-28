import NDO_JFz_TX2_Q1_Dots0
import NDO_JFv_TX2_Query0Formula
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨88917192,1404912867⟩,⟨1133588453,1994713957⟩⟩,⟨⟨1568263249,1326122172⟩,⟨227384155,1073535207⟩⟩⟩
def h1 : FE := ⟨⟨⟨1116233815,672804777⟩,⟨1259957715,1980269924⟩⟩,⟨⟨1647517551,1619765091⟩,⟨824383503,1922323962⟩⟩⟩
def h2 : FE := ⟨⟨⟨1642783305,1487036343⟩,⟨914189169,341700253⟩⟩,⟨⟨1186184942,2018132988⟩,⟨1078158410,1172338886⟩⟩⟩
def h3 : FE := ⟨⟨⟨1284801390,342711987⟩,⟨459655913,646879850⟩⟩,⟨⟨1877136341,1393228055⟩,⟨531065529,1217953218⟩⟩⟩
def t2 : FE := ⟨⟨⟨858635299,1797784812⟩,⟨770594285,1784030139⟩⟩,⟨⟨108875816,219195152⟩,⟨1552361144,867255641⟩⟩⟩
def t1 : FE := ⟨⟨⟨1344789111,2066640265⟩,⟨1402646385,724057239⟩⟩,⟨⟨754099,894949342⟩,⟨364513955,1193024241⟩⟩⟩
def value : FE := ⟨⟨⟨12674944,1246410058⟩,⟨116774269,918536601⟩⟩,⟨⟨1000197073,68609528⟩,⟨19935596,1874953030⟩⟩⟩
theorem quarter : (4:FE)⁻¹=536870912 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem horner2 : h2+alpha*h3=t2 := by
  unfold h2 alpha h3 t2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem horner1 : h1+alpha*t2=t1 := by
  unfold h1 alpha t2 t1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem horner0 : h0+alpha*t1=value := by
  unfold h0 alpha t1 value
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms quarter
#print axioms horner2
#print axioms horner1
#print axioms horner0
end AspisR1.JFz_TX2_Q1_CircleNumbers
end
