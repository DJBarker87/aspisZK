import NLM_SevenSites
set_option autoImplicit false
noncomputable section
namespace NLM_WrapperSnapshot2
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry NLM_Snapshot NLM_SevenSites
/-- Source occurrence 2, from the SAME preceding owned list and SDK state.
This is support for the parent fold; native copy/allocation association is pending. -/
theorem step (e : Entry) :
 NLM_Snapshot.G (before e 2) 2 192 192 (.ok ())=
 ⟨.ok (e.snapshot 2 192 192,before e 3),
   normalEvents (before e 2) 2 192 192⟩ := by
 have h := NLM_Snapshot.normal e 2 2 192 192
  (NLM_SevenSnapshots.ownedValues e (sites.take 2))
 simpa [before,returned,ready,NLM_SevenSnapshots.ownedValues,sites,List.take,List.map,List.append] using h
#print step
#print axioms step
end NLM_WrapperSnapshot2
