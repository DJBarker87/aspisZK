import NDO_JGv_QueryScalars2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars3
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars2.rhs
abbrev beforePower := JGv_QueryScalars2.power
def product : E := ⟨⟨⟨1069961892#u32,1323855474#u32⟩,⟨191837497#u32,484279162#u32⟩⟩,⟨⟨601612890#u32,947097477#u32⟩,⟨1265013945#u32,1870047227#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨1909128893#u32,669593331#u32⟩,⟨1866068215#u32,2027219784#u32⟩⟩,⟨⟨2127250229#u32,377843161#u32⟩,⟨906344362#u32,1930853491#u32⟩⟩⟩
def power : K := ⟨⟨628207122#u32,407872079#u32⟩,⟨1058681237#u32,1402462633#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨3,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars3
end
