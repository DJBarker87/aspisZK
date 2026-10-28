import NDO_JFu_MaskGather
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskTotal
open Aeneas Aeneas.Std Result FIp_SemanticArithmetic JFu_MaskInputs

/-- The installed mask actually returns on the same decoded real-byte inputs. -/
theorem source : ∃ out,FIp_SemanticArithmetic.mask c1 maskOnly g point=ok out ∧
    FIp_SemanticValues.Canon out := by
  obtain ⟨native,call,canonical,_⟩ := FIp_MaskValue.source c1 maskOnly g point
    c1_canonical maskOnly_canonical point_canonical g_canonical
  exact ⟨fromProbe native,call,canonical⟩

#print axioms source
end AspisR1.JFu_MaskTotal
end
