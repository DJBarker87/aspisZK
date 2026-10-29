import R1Z.PV_OWNB_ActualPrefix
import R1Z.PV_OWNB_ActualFold
import R1Z.PV_OWNB_ValueFold
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualValues
open PV_OWNB_Cursor PV_OWN_Link PV_OWN_Bytes

theorem step (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor) :
 PV_OWNB_Prefix.values (PV_OWNB_ActualFilter.step keep bytes q)=
 PV_OWNB_Prefix.values q++(if keep (q.source q.read) then [q.source q.read] else []) := by
 unfold PV_OWNB_ActualFilter.step
 split
 · rw [PV_OWNB_ActualPrefix.sink,PV_OWNB_Prefix.advance]
 · rw [PV_OWNB_Prefix.advance,List.append_nil]

theorem values (keep : Link → Bool) (bytes : Nat → Link → Bytes) (n : Nat) (q : Cursor) :
 PV_OWNB_Prefix.values (PV_OWNB_ActualFold.run keep bytes n q)=
 PV_OWNB_Prefix.values q++PV_OWNB_ValueFold.selected keep q.source q.read n := by
 induction n generalizing q with
 | zero => simp [PV_OWNB_ActualFold.run,PV_OWNB_ValueFold.selected]
 | succ n ih =>
  rw [PV_OWNB_ActualFold.run,ih,step,
   PV_OWNB_ActualFilter.advances,PV_OWNB_ActualFilter.source]
  simp only [PV_OWNB_ValueFold.selected,List.append_assoc]
#print axioms step
#print axioms values
end R1Z.PV_OWNB_ActualValues
