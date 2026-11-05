import NGD_RowPayload
import NFU_RowDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticDomains
/-- Every original row supplies the SAME bounded child windows and disjoint
output, independently of any expansion reply. -/
theorem row (r : Nat) (live : r<27) :
 NGD_SemanticSchedule.src r+5+NGD_SemanticSchedule.stored r≤7015 ∧
 NGD_SemanticSchedule.dst r+5+NFU_PacketDomains.payloadSize r≤13831 ∧
 NGD_SemanticSchedule.stored r≤1856 ∧
 NFU_PacketDomains.payloadSize r≤3712 ∧
 (14≤r→NGD_SemanticSchedule.stored r%16=0 ∧
   NFU_PacketDomains.payloadSize r=2*NGD_SemanticSchedule.stored r) ∧
 (∀ later,r<later→later<27→NGD_SemanticSchedule.dst r+5+
   NFU_PacketDomains.payloadSize r≤NGD_SemanticSchedule.dst later) := by
 obtain ⟨source,destination,compact,full⟩:=NGD_SemanticSchedule.windows r live
 exact ⟨source,destination,compact,full,
   fun high=>NGD_SemanticSchedule.expansion_domain r high live,
   fun later order bound=>NGD_SemanticSchedule.disjoint r later order bound⟩
#print axioms row
end NGV_SemanticDomains
