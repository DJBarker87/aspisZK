import R1Z.PV_OWNB_ActualValues
import R1Z.PV_OWNB_ActualIdentity
import R1Z.PV_OWNB_ActualComplete
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualResult
open PV_OWNB_Cursor PV_OWN_Link PV_OWN_Bytes PV_OWNB_Padding
/-- All padding choices are quantified. Native store-copy adequacy remains explicit. -/
theorem complete (q : Cursor) (keep : Link → Bool) (bytes : Nat → Link → Bytes)
 (h:Valid q) (copy:∀ i v, Agrees (PV_OWNB_LinkBytes.encode v) (bytes i v)) :
 let final:=PV_OWNB_ActualFold.run keep bytes (q.length-q.read) q
 Valid final ∧ final.read=final.length ∧
 final.token=q.token ∧ final.memory.generations=q.memory.generations ∧
 PV_OWNB_Prefix.values final=PV_OWNB_Prefix.values q++
 (PV_OWNB_ValueFold.input q.source q.read (q.length-q.read)).filter keep := by
 obtain ⟨hv,hd⟩:=PV_OWNB_ActualComplete.complete keep bytes q h copy
 obtain ⟨ht,hg⟩:=PV_OWNB_ActualIdentity.generation keep bytes (q.length-q.read) q
 refine ⟨hv,hd,ht,hg,?_⟩
 rw [PV_OWNB_ActualValues.values,PV_OWNB_ValueFold.filter]
#print axioms complete
end R1Z.PV_OWNB_ActualResult
