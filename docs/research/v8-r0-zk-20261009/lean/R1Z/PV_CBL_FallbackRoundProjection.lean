import R1Z.PV_CBL_FallbackRoundComplete
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackRoundProjection
open PV_CBL_FallbackArray4
set_option autoImplicit false
/-- Complete-Result helper certificates retain each lane, without scalar evaluation. -/
theorem lane (a b w : A4) (i : Usize) :
    (do let r ← PV_CBL_FallbackRound.sha_fallback_reference.extracted_round a b w
        Array.index_usize r i) =
    Array.index_usize (PV_CBL_FallbackRoundComplete.output a b w) i := by
  rw [PV_CBL_FallbackRoundComplete.complete]
  rfl
#print axioms lane
end R1Z.PV_CBL_FallbackRoundProjection
