import NDO_JGg_ScalarForward
set_option autoImplicit false
namespace AspisR1.JGg_Powers
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge

theorem source (N : Usize) (x : PE)
    (canonical : AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE x)) :
    ∃ out,powersPublic N x=ok out := by
  obtain ⟨out,call,meaning⟩ := AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact N (toClaimE x) canonical
  refine ⟨mapArray fromClaimE out,?_⟩
  unfold powersPublic
  rw [call,bind_tc_ok]
#print axioms source
end AspisR1.JGg_Powers
