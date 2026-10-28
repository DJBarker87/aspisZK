import NDO_JFu_PublicSemantic
import NDO_JFs_SerializerCanonical
import RPv_FIy_NativeCoefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PublicCanonical
open Aeneas Aeneas.Std Result FIq_Native
abbrev p := JFu_PublicSemantic.value
abbrev P := FIw_ScalarArithmetic.P

theorem digest (d : Array U32 8#usize) (h : JFu_DigestCanonical.Canonical d) : ∀ x∈d.val,x.val<P := by
  intro x hx
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hx
  subst x
  exact h ⟨i,by simpa only [d.property,show (8#usize).val=8 from rfl] using hi⟩
#print axioms digest

theorem anchor : ∀ x∈p.anchor.val,x.val<P := digest _ JFt_Digest43.canonical
#print axioms anchor

theorem nullifier : ∀ x∈p.nullifier.val,x.val<P := digest _ JFt_Digest44.canonical
#print axioms nullifier

theorem recipient : ∀ r,p.recipient=some r → ∀ x∈r.val,x.val<P := by
  intro r hr
  have same : r=JFt_Digest45.value := (Option.some.inj hr).symm
  subst r
  exact digest _ JFt_Digest45.canonical
#print axioms recipient

theorem change : ∀ x∈p.change.val,x.val<P := digest _ JFt_Digest46.canonical
#print axioms change

theorem asset : p.asset_id.val<P := by change (77:Nat)<2147483647;omega
#print axioms asset

theorem amount : (p.withdrawal_amount.getD 0#u32).val<P := by change (0:Nat)<2147483647;omega
#print axioms amount
end AspisR1.JFy_PublicCanonical
end
