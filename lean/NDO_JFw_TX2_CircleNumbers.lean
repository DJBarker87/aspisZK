import NDO_JFw_TX2_Dots0
import NDO_JFv_TX2_Query0Formula
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_CircleNumbers
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
def alpha : FE := ⟨⟨⟨492967452,709301790⟩,⟨1617612614,599334322⟩⟩,⟨⟨1668486716,1253062525⟩,⟨341779229,880523595⟩⟩⟩
def h0 : FE := ⟨⟨⟨844740459,754830121⟩,⟨449810043,1912379234⟩⟩,⟨⟨1766376126,1593456259⟩,⟨679341998,88703612⟩⟩⟩
def h1 : FE := ⟨⟨⟨1962460957,1542716725⟩,⟨1875832555,945834832⟩⟩,⟨⟨1792143810,338668181⟩,⟨562462294,187012999⟩⟩⟩
def h2 : FE := ⟨⟨⟨1851154795,348294045⟩,⟨204013600,1850419426⟩⟩,⟨⟨909473564,842544530⟩,⟨1384702564,681215315⟩⟩⟩
def h3 : FE := ⟨⟨⟨1241464328,1934926670⟩,⟨1894582285,524959833⟩⟩,⟨⟨1099086019,2096763102⟩,⟨1844491127,1633598707⟩⟩⟩
def t2 : FE := ⟨⟨⟨881680309,1837214753⟩,⟨1820746978,544366712⟩⟩,⟨⟨1192078489,783806444⟩,⟨2049867192,1378303196⟩⟩⟩
def t1 : FE := ⟨⟨⟨1184302853,281272162⟩,⟨2008233893,278233603⟩⟩,⟨⟨449342319,890749118⟩,⟨602902576,20910592⟩⟩⟩
def value : FE := ⟨⟨⟨2028222263,814288248⟩,⟨354118641,1376248873⟩⟩,⟨⟨1642244954,2101120408⟩,⟨22065465,1602413776⟩⟩⟩
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
end AspisR1.JFw_TX2_CircleNumbers
end
