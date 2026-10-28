import NDO_JGv_QueryScalars10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars11
open Aeneas Aeneas.Std Result
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
abbrev beforeRhs := JGv_QueryScalars10.rhs
abbrev beforePower := JGv_QueryScalars10.power
def product : E := ⟨⟨⟨1623090827#u32,250797147#u32⟩,⟨279887117#u32,541803551#u32⟩⟩,⟨⟨955608094#u32,128538506#u32⟩,⟨767401678#u32,2077704916#u32⟩⟩⟩
def rhs : E := ⟨⟨⟨429739680#u32,695123492#u32⟩,⟨846004517#u32,43341797#u32⟩⟩,⟨⟨1191479073#u32,219638325#u32⟩,⟨1188620633#u32,2137727829#u32⟩⟩⟩
def power : K := ⟨⟨201596191#u32,1808251096#u32⟩,⟨1349023452#u32,1445656127#u32⟩⟩
theorem multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue ⟨11,by decide⟩) beforePower=ok product := by
  with_unfolding_all rfl
#print axioms multiply
theorem addition : SAQ_Arithmetic.add beforeRhs product=ok rhs := by with_unfolding_all rfl
#print axioms addition
theorem advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power := by with_unfolding_all rfl
#print axioms advance
end AspisR1.JGv_QueryScalars11
end
