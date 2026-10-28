import NDO_JGv_QueryScalars5
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars6
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars5.rhs
abbrev beforePower := JGv_QueryScalars5.power
def product : E := ⟨⟨⟨883188833#u32,1299447423#u32⟩,⟨1389521830#u32,779325391#u32⟩⟩,⟨⟨893727846#u32,554597766#u32⟩,⟨542101017#u32,783642376#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨1188916110#u32,1081840799#u32⟩,⟨581813589#u32,1017243990#u32⟩⟩,⟨⟨1391134497#u32,908470858#u32⟩,⟨728742447#u32,387836838#u32⟩⟩⟩
def power : K := ⟨⟨1020978336#u32,1617602641#u32⟩,⟨1214100188#u32,2078772288#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨6,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars6
end
