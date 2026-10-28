import NDO_JGv_QueryScalars4
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars5
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars4.rhs
abbrev beforePower := JGv_QueryScalars4.power
def product : E := ⟨⟨⟨2002986252#u32,1892559905#u32⟩,⟨1236319019#u32,1928470416#u32⟩⟩,⟨⟨1899723642#u32,1769322702#u32⟩,⟨1753738827#u32,917051066#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨305727277#u32,1929877023#u32⟩,⟨1339775406#u32,237918599#u32⟩⟩,⟨⟨497406651#u32,353873092#u32⟩,⟨186641430#u32,1751678109#u32⟩⟩⟩
def power : K := ⟨⟨91329361#u32,1482788473#u32⟩,⟨2048525372#u32,1937922895#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨5,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars5
end
