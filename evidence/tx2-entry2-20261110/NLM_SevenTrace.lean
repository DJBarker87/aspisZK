import NLM_SevenSnapshots
set_option autoImplicit false
noncomputable section
namespace NLM_SevenSnapshots
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLM_Snapshot

def chronological (e : Entry) : Nat → List NLM_Snapshot.Owned → List Site → List NLM_Snapshot.Event
 | _,_,[] => []
 | t,owned,c::cs =>
   normalEvents (ready e t owned) c.account c.lo c.hi ++
   chronological e (t+1) (owned++[e.snapshot c.account c.lo c.hi]) cs
/-- The SAME returned state and the full token/allocator/return event prefix
are composed at every site, including snapshots whose bytes contain Err. -/
theorem normal (e : Entry) (t : Nat) (owned : List NLM_Snapshot.Owned) (cs : List Site) :
 G (fun _ => .ok ()) cs (ready e t owned)=
 ⟨.ok (ready e (t+cs.length) (owned++ownedValues e cs)),chronological e t owned cs⟩ := by
 induction cs generalizing t owned with
 | nil => simp [G,chronological,ownedValues,ready,Pure.pure]
 | cons c cs ih =>
   rw [G,NLM_Snapshot.normal]
   change (⟨(G (fun _ => .ok ()) cs (ready e (t+1) (owned++[e.snapshot c.account c.lo c.hi]))).result,
    normalEvents (ready e t owned) c.account c.lo c.hi ++
      (G (fun _ => .ok ()) cs (ready e (t+1) (owned++[e.snapshot c.account c.lo c.hi]))).events⟩ : NLM_Snapshot.Run NLM_Snapshot.State) = _
   rw [ih]
   simp [chronological,ownedValues,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
#print normal
#print axioms normal
end NLM_SevenSnapshots
