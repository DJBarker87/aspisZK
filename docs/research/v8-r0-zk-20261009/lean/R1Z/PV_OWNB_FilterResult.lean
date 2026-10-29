import R1Z.PV_OWNB_ValueFold
import R1Z.PV_OWNB_FilterComplete
import R1Z.PV_OWNB_CursorStart
set_option autoImplicit false
namespace R1Z.PV_OWNB_FilterResult
open PV_OWNB_Cursor PV_OWN_Heap PV_OWNB_LinkCodec PV_OWN_Link
/-- Complete byte/value law for the explicitly defined scoped filtering model. -/
theorem complete (q : Cursor) (keep : Link → Bool) (h:PV_OWNB_Cursor.Valid q) :
 let final:=PV_OWNB_FilterFold.run keep (q.length-q.read) q
 PV_OWNB_Cursor.Valid final ∧ final.read=final.length ∧
 final.token=q.token ∧ final.memory.generations=q.memory.generations ∧
 PV_OWNB_Prefix.values final=PV_OWNB_Prefix.values q++
 (PV_OWNB_ValueFold.input q.source q.read (q.length-q.read)).filter keep := by
 obtain ⟨hv,hd⟩:=PV_OWNB_FilterComplete.complete keep q h
 obtain ⟨ht,hg⟩:=PV_OWNB_FilterIdentity.generation keep (q.length-q.read) q
 refine ⟨hv,hd,ht,hg,?_⟩
 rw [PV_OWNB_ValueFold.values,PV_OWNB_ValueFold.filter]
#print axioms complete
end R1Z.PV_OWNB_FilterResult
