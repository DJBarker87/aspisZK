import NJE_Pow5Packet

set_option autoImplicit false
noncomputable section
namespace NJE_Pow5Realization
open Aeneas Aeneas.Std Result

theorem cut (x : U32) : NJA_Pow5Cut.Cut x (NJE_Pow5Packet.events x) 3 (NJE_Pow5Packet.result x) := by
 refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
 intro i
 fin_cases i <;> rfl

theorem law (x : U32) :
    NJA_FieldLaws.pow5_ref x=ok (NJE_Pow5Packet.result x) ∧
    (NJE_Pow5Packet.result x).val<2147483647 ∧
    ((NJE_Pow5Packet.result x).val:NJA_Pow5Model.K)=R0P.poseidonPow5 (x.val:NJA_Pow5Model.K) :=
 NJE_Pow5Packet.TX1_307 x 3 (NJE_Pow5Packet.result x) (cut x)

#print cut
#print axioms cut
#print law
#print axioms law
end NJE_Pow5Realization
end
