import NFU_CompactLeaves
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ExpandPacket
open NFU_Retarget
/-- Construct the CLOSED expansion leaf's entire returned carrier from its
original source and SAME output window. No supplied trace or successful reply. -/
theorem result (bytes before : Slice U8)
 (bound : bytes.val.length≤1856) (aligned : bytes.val.length%16=0)
 (shape : before.val.length=2*bytes.val.length) :
 ∃ after : Slice U8,
 NFU_Retarget.compact.expand_values bytes before=ok (.Ok (),after) ∧
 after.val.length=before.val.length ∧
 (∀ j,j<before.val.length→after.val[j]?.getD 0#u8=LPl_A.Expand.byte bytes.val j) := by
 obtain ⟨after,trace⟩:=LPn.Expand.total bytes.val before.val (bytes.val.length/16)
 have inherited:=LPn.Expand.to_inherited bytes.val before.val after _ trace
 have length:=LPl.Expand.length bytes.val before.val after _ inherited
 let output : Slice U8:=⟨after,by rw [length];exact before.property⟩
 refine ⟨output,NFU_CompactLeaves.expand_result bytes before output bound aligned shape trace,length,?_⟩
 intro j live
 have point:=LPl.Expand.invariant bytes.val before.val after _ inherited j live
 have complete : j<32*(bytes.val.length/16) := by omega
 simpa only [if_pos complete] using point
#print axioms result
end NGV_ExpandPacket
