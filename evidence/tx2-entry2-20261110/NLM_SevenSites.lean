import NLM_SevenSnapshots
set_option autoImplicit false
noncomputable section
namespace NLM_SevenSites
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
open NLM_SevenSnapshots NLM_Snapshot
/-- Frozen stage2:471-477, in exact source order. -/
def sites : List Site := [⟨0,58295,58295⟩,⟨1,384,384⟩,⟨2,192,192⟩,
 ⟨3,768,768⟩,⟨4,128,256⟩,⟨5,192,320⟩,⟨6,1768,1768⟩]
def before (e : Entry) (i : Nat) : NLM_Snapshot.State :=
 ready e i (ownedValues e (sites.take i))
/-- All seven snapshots run even if their returned bytes contain a deferred
error. The final account/cell state restores and token allocation advances7. -/
theorem all_results (e : Entry) :
 (NLM_SevenSnapshots.G (fun _ => .ok ()) sites (ready e 0 [])).result=
 .ok (ready e 7 (ownedValues e sites)) := by
 simpa [sites] using NLM_SevenSnapshots.normal_result e 0 [] sites
#print all_results
#print axioms all_results
end NLM_SevenSites
