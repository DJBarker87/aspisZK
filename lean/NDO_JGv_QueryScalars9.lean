import NDO_JGv_QueryScalars8
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars9
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars8.rhs
abbrev beforePower := JGv_QueryScalars8.power
def product : E := ⟨⟨⟨424001549#u32,195033569#u32⟩,⟨1870474544#u32,1715914579#u32⟩⟩,⟨⟨217891717#u32,1541456227#u32⟩,⟨350882286#u32,1130477626#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨935449906#u32,1062492223#u32⟩,⟨1425555704#u32,286811443#u32⟩⟩,⟨⟨1349768666#u32,856427771#u32⟩,⟨289830187#u32,2020416301#u32⟩⟩⟩
def power : K := ⟨⟨1092787441#u32,1337699776#u32⟩,⟨503189878#u32,1865276895#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨9,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars9
end
