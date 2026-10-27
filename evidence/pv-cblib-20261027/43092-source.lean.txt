import R1Z.PV_CBL_FallbackBlockTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackBlockOutcomes
set_option autoImplicit false
theorem success (s : Array U32 8#usize) (b : Array U32 16#usize) :
    ∃ r, PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block s b = ok r :=
  PV_CBL_FallbackBlockTotal.total s b
theorem no_error (s : Array U32 8#usize) (b : Array U32 16#usize) (e : Error) :
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block s b ≠ fail e := by
  obtain ⟨r,hr⟩ := success s b
  rw [hr]
  intro h
  cases h
theorem unique (s : Array U32 8#usize) (b : Array U32 16#usize) (r t : Array U32 8#usize)
    (hr : PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block s b = ok r)
    (ht : PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block s b = ok t) : r=t := by
  have h : ok r = (ok t : Result (Array U32 8#usize)) := hr.symm.trans ht
  exact Result.ok.inj h
#print axioms success
#print axioms no_error
#print axioms unique
end R1Z.PV_CBL_FallbackBlockOutcomes
