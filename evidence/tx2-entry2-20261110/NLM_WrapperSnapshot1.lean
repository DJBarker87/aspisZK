import NLM_SevenSites
set_option autoImplicit false
noncomputable section
namespace NLM_WrapperSnapshot1
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry NLM_Snapshot NLM_SevenSites
/-- Source occurrence 1, from the SAME preceding owned list and SDK state.
This is support for the parent fold; native copy/allocation association is pending. -/
theorem step (e : Entry) :
 NLM_Snapshot.G (before e 1) 1 384 384 (.ok ())=
 ⟨.ok (e.snapshot 1 384 384,before e 2),
   normalEvents (before e 1) 1 384 384⟩ := by
 have h := NLM_Snapshot.normal e 1 1 384 384
  (NLM_SevenSnapshots.ownedValues e (sites.take 1))
 simpa [before,returned,ready,NLM_SevenSnapshots.ownedValues,sites,List.take,List.map,List.append] using h
#print step
#print axioms step
end NLM_WrapperSnapshot1
