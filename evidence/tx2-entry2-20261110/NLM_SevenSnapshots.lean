import NLM_SnapshotTrace
set_option autoImplicit false
noncomputable section
namespace NLM_SevenSnapshots
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
open NLM_Snapshot
structure Site where
 account : Nat
 lo : Nat
 hi : Nat
/-- One State returned by a snapshot is passed directly to the next site.
The allocator occurrence result is attached to THAT source site; this is an
intermediate source fold until actual allocator/cut instantiation is installed. -/
def G (allocation : Site → Result Unit) : List Site → State → Run State
 | [],s => pure s
 | c::cs,s => do
   let (_,post) ← NLM_Snapshot.G s c.account c.lo c.hi (allocation c)
   G allocation cs post

def ownedValues (e : Entry) (cs : List Site) : List NLM_Snapshot.Owned :=
 cs.map (fun c => e.snapshot c.account c.lo c.hi)
/-- Symbolic fold; no 58k-cell evaluation. Every deferred bytes error remains
inside its owned value and does not prevent the later six acquisitions. -/
theorem normal_result (e : Entry) (t : Nat) (owned : List NLM_Snapshot.Owned) (cs : List Site) :
 (G (fun _ => .ok ()) cs (ready e t owned)).result=
 .ok (ready e (t+cs.length) (owned++ownedValues e cs)) := by
 induction cs generalizing t owned with
 | nil => simp [G,ownedValues,ready,NJU_Log.erase_pure]
 | cons c cs ih =>
   simp only [G,NJU_Log.erase_bind]
   rw [NLM_Snapshot.normal_result]
   change (G (fun _ => .ok ()) cs (ready e (t+1) (owned++[e.snapshot c.account c.lo c.hi]))).result=_
   rw [ih]
   simp [ownedValues,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
#print G
#print normal_result
#print axioms normal_result
end NLM_SevenSnapshots
