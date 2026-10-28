import NDO_JGv_QueryScalars1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars2
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars1.rhs
abbrev beforePower := JGv_QueryScalars1.power
def product : E := ⟨⟨⟨112698842#u32,621400019#u32⟩,⟨1914168382#u32,741360314#u32⟩⟩,⟨⟨413758039#u32,1072743503#u32⟩,⟨1289427661#u32,854870988#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨839167001#u32,1493221504#u32⟩,⟨1674230718#u32,1542940622#u32⟩⟩,⟨⟨1525637339#u32,1578229331#u32⟩,⟨1788814064#u32,60806264#u32⟩⟩⟩
def power : K := ⟨⟨2007733475#u32,54273399#u32⟩,⟨760590275#u32,8519774#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨2,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars2
end
