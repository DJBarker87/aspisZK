import NDO_JGv_QueryScalars0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars1
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars0.rhs
abbrev beforePower := JGv_QueryScalars0.power
def product : E := ⟨⟨⟨706961658#u32,453228870#u32⟩,⟨1394821810#u32,2126452343#u32⟩⟩,⟨⟨552526844#u32,1469734419#u32⟩,⟨17916476#u32,731429598#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨726468159#u32,871821485#u32⟩,⟨1907545983#u32,801580308#u32⟩⟩,⟨⟨1111879300#u32,505485828#u32⟩,⟨499386403#u32,1353418923#u32⟩⟩⟩
def power : K := ⟨⟨1480511457#u32,834430317#u32⟩,⟨1472072787#u32,354167411#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨1,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars1
end
