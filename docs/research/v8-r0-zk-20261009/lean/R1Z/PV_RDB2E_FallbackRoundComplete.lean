import R1Z.PV_RDB2E_FallbackRoundTotal

section
-- Unchanged source component R1Z.PV_CBL_FallbackRoundComplete
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundComplete
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar PV_CBL_FallbackRoundTotal
set_option autoImplicit false
def inputState (cdgh abef : A4) : State :=
  ⟨abef.val[0]!,abef.val[1]!,cdgh.val[0]!,cdgh.val[1]!,
   abef.val[2]!,abef.val[3]!,cdgh.val[2]!,cdgh.val[3]!⟩
def output (cdgh abef wk : A4) : A4 :=
  let r := step (step (inputState cdgh abef) wk.val[3]!) wk.val[2]!
  pack r.a r.b r.e r.f
theorem complete (cdgh abef wk : A4) :
    PV_CBL_FallbackRound.sha_fallback_reference.extracted_round cdgh abef wk =
      ok (output cdgh abef wk) := by
  have h := PV_CBL_FallbackRoundShape.shape (inputState cdgh abef)
    wk.val[3]! wk.val[2]! wk.val[0]! wk.val[1]!
  simpa only [PV_CBL_FallbackRound.sha_fallback_reference.extracted_round,
    inputState,output,pack_eta] using h
theorem total (cdgh abef wk : A4) :
    ∃ r, PV_CBL_FallbackRound.sha_fallback_reference.extracted_round cdgh abef wk = ok r :=
  ⟨output cdgh abef wk,complete cdgh abef wk⟩
theorem no_failure (cdgh abef wk : A4) (e : Error) :
    PV_CBL_FallbackRound.sha_fallback_reference.extracted_round cdgh abef wk ≠ fail e := by
  rw [complete]
  intro h
  cases h
#print axioms inputState
#print axioms output
#print axioms complete
#print axioms total
#print axioms no_failure
end R1Z.PV_CBL_FallbackRoundComplete

end
