import NJA_Compress

set_option autoImplicit false
noncomputable section
namespace NJE_AddValue
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K

def add (x c : U32) : U32 :=
 if h : x.val<2147483647 ∧ c.val<2147483647 then
   Classical.choose (NJA_Compress.add_law x c h.1 h.2)
 else 0#u32

theorem law (x c : U32) (hx : x.val<2147483647) (hc : c.val<2147483647) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.add x c=ok (add x c) ∧
    (add x c).val<2147483647 ∧
    ((add x c).val:K)=(x.val:K)+(c.val:K) := by
 simpa only [add,dif_pos (And.intro hx hc)] using
   Classical.choose_spec (NJA_Compress.add_law x c hx hc)

#print law
#print axioms law
end NJE_AddValue
end
