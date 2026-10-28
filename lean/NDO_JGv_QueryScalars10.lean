import NDO_JGv_QueryScalars9
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars10
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars9.rhs
abbrev beforePower := JGv_QueryScalars9.power
def product : E := ⟨⟨⟨18682594#u32,1529317769#u32⟩,⟨1288045343#u32,1362210450#u32⟩⟩,⟨⟨1033585960#u32,1382155695#u32⟩,⟨131388768#u32,187090259#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨954132500#u32,444326345#u32⟩,⟨566117400#u32,1649021893#u32⟩⟩,⟨⟨235870979#u32,91099819#u32⟩,⟨421218955#u32,60022913#u32⟩⟩⟩
def power : K := ⟨⟨330188972#u32,1891336153#u32⟩,⟨1917171426#u32,1035348157#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨10,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars10
end
