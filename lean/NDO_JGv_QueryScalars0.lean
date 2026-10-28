import NDO_JFz_TX2_Gates
import JFn_QueryArithmeticTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars0
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
def beforeRhs : E := ⟨⟨⟨1460949651#u32,1897962060#u32⟩,⟨2049955535#u32,440526196#u32⟩⟩,⟨⟨1936630531#u32,105592648#u32⟩,⟨1567937285#u32,2130692216#u32⟩⟩⟩
def beforePower : K := ⟨⟨1007926423#u32,526023474#u32⟩,⟨347718395#u32,268326460#u32⟩⟩
def product : E := ⟨⟨⟨706040497#u32,668114202#u32⟩,⟨610252285#u32,382085416#u32⟩⟩,⟨⟨770205572#u32,1077642408#u32⟩,⟨1061016289#u32,638780756#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨19506501#u32,418592615#u32⟩,⟨512724173#u32,822611612#u32⟩⟩,⟨⟨559352456#u32,1183235056#u32⟩,⟨481469927#u32,621989325#u32⟩⟩⟩
def power : K := ⟨⟨746258009#u32,1818240317#u32⟩,⟨352046373#u32,1373647064#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨0,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars0
end
