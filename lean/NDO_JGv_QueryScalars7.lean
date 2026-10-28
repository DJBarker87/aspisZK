import NDO_JGv_QueryScalars6
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars7
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars6.rhs
abbrev beforePower := JGv_QueryScalars6.power
def product : E := ⟨⟨⟨1439825359#u32,1640690495#u32⟩,⟨1896642296#u32,882461157#u32⟩⟩,⟨⟨1703940683#u32,1032813356#u32⟩,⟨822667487#u32,1363723243#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨481257822#u32,575047647#u32⟩,⟨330972238#u32,1899705147#u32⟩⟩,⟨⟨947591533#u32,1941284214#u32⟩,⟨1551409934#u32,1751560081#u32⟩⟩⟩
def power : K := ⟨⟨1335767277#u32,1698648098#u32⟩,⟨2067346409#u32,114406496#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨7,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars7
end
