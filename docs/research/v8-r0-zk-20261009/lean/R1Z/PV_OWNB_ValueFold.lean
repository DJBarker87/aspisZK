import R1Z.PV_OWNB_FilterIdentity
import R1Z.PV_OWNB_FilterValues
set_option autoImplicit false
namespace R1Z.PV_OWNB_ValueFold
open PV_OWNB_Cursor PV_OWN_Link

def selected (keep : Link → Bool) (source : Nat → Link) : Nat → Nat → List Link
 | _,0 => []
 | start,n+1 => (if keep (source start) then [source start] else [])++selected keep source (start+1) n

def input (source : Nat → Link) : Nat → Nat → List Link
 | _,0 => []
 | start,n+1 => source start::input source (start+1) n

theorem filter (keep : Link → Bool) (source : Nat → Link) (start n : Nat) :
 selected keep source start n=(input source start n).filter keep := by
 induction n generalizing start with
 | zero => rfl
 | succ n ih =>
  simp only [selected,input,List.filter_cons]
  rw [ih]
  split <;> simp_all

theorem values (keep : Link → Bool) (n : Nat) (q : Cursor) :
 PV_OWNB_Prefix.values (PV_OWNB_FilterFold.run keep n q)=
 PV_OWNB_Prefix.values q++selected keep q.source q.read n := by
 induction n generalizing q with
 | zero => simp [PV_OWNB_FilterFold.run,selected]
 | succ n ih =>
  rw [PV_OWNB_FilterFold.run,ih,PV_OWNB_FilterValues.step,
   PV_OWNB_FilterStep.advances,PV_OWNB_FilterValues.source]
  simp only [selected,List.append_assoc]
attribute [local irreducible] selected input
#print axioms filter
#print axioms values
end R1Z.PV_OWNB_ValueFold
