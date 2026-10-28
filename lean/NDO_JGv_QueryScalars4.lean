import NDO_JGv_QueryScalars3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars4
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars3.rhs
abbrev beforePower := JGv_QueryScalars3.power
def product : E := ⟨⟨⟨688579426#u32,1515207434#u32⟩,⟨384871819#u32,577195693#u32⟩⟩,⟨⟨765400074#u32,354190876#u32⟩,⟨1821525535#u32,1051257199#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨450224672#u32,37317118#u32⟩,⟨103456387#u32,456931830#u32⟩⟩,⟨⟨745166656#u32,732034037#u32⟩,⟨580386250#u32,834627043#u32⟩⟩⟩
def power : K := ⟨⟨1065362722#u32,149339928#u32⟩,⟨711045811#u32,1460956558#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨4,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars4
end
