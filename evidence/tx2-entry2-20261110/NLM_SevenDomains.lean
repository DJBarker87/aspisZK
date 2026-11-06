import NLM_StorageFacts
set_option autoImplicit false
noncomputable section
namespace NLM_SevenDomains
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry
/-- CLOSED getter domains at the seven exact snapshot call sites. -/
theorem account0 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 0 58295 58295) :=
 NLM_StorageFacts.snapshot e 0 58295#usize 58295#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
theorem account1 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 1 384 384) :=
 NLM_StorageFacts.snapshot e 1 384#usize 384#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
theorem account2 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 2 192 192) :=
 NLM_StorageFacts.snapshot e 2 192#usize 192#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
theorem account3 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 3 768 768) :=
 NLM_StorageFacts.snapshot e 3 768#usize 768#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
theorem account4 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 4 128 256) :=
 NLM_StorageFacts.snapshot e 4 128#usize 256#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
theorem account5 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 5 192 320) :=
 NLM_StorageFacts.snapshot e 5 192#usize 320#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
theorem account6 (e : Entry) : NGL_StorageCases.Domain (e.snapshot 6 1768 1768) :=
 NLM_StorageFacts.snapshot e 6 1768#usize 1768#usize (by unfold NGL_StorageCases.Allowed; decide) (by unfold NGL_StorageCases.Allowed; decide)
#print axioms account0
#print axioms account1
#print axioms account2
#print axioms account3
#print axioms account4
#print axioms account5
#print axioms account6
end NLM_SevenDomains
