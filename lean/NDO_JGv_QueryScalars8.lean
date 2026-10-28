import NDO_JGv_QueryScalars7
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars8
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars7.rhs
abbrev beforePower := JGv_QueryScalars7.power
def product : E := ⟨⟨⟨30190535#u32,292411007#u32⟩,⟨1371592569#u32,966159011#u32⟩⟩,⟨⟨184285416#u32,1668654624#u32⟩,⟨535021614#u32,1285862241#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨511448357#u32,867458654#u32⟩,⟨1702564807#u32,718380511#u32⟩⟩,⟨⟨1131876949#u32,1462455191#u32⟩,⟨2086431548#u32,889938675#u32⟩⟩⟩
def power : K := ⟨⟨837112873#u32,1704035042#u32⟩,⟨988032166#u32,965014931#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨8,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars8
end
