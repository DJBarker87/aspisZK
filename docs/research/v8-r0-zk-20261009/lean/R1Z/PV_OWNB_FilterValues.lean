import R1Z.PV_OWNB_Prefix
import R1Z.PV_OWNB_FilterStep
set_option autoImplicit false
namespace R1Z.PV_OWNB_FilterValues
open PV_OWNB_Cursor PV_OWN_Link

theorem step (keep : Link → Bool) (q : Cursor) :
 PV_OWNB_Prefix.values (PV_OWNB_FilterStep.step keep q)=
 PV_OWNB_Prefix.values q++(if keep (q.source q.read) then [q.source q.read] else []) := by
 unfold PV_OWNB_FilterStep.step
 split
 · rw [PV_OWNB_Prefix.sink,PV_OWNB_Prefix.advance]
 · rw [PV_OWNB_Prefix.advance,List.append_nil]

theorem source (keep : Link → Bool) (q : Cursor) :
 (PV_OWNB_FilterStep.step keep q).source=q.source := by
 unfold PV_OWNB_FilterStep.step
 split <;> rfl
#print axioms step
#print axioms source
end R1Z.PV_OWNB_FilterValues
