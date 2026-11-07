import NNG_LIBTerminal
import NNG_LIBClaimsDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TerminalReturned136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain

theorem canonical (fallback : Value) (pub : LIB_VCarriers.Public) (claims : Claims) (alpha : Alpha)
    (orig : LIB_VCarriers.OrigChallenges) (q : Q)
    (claimsDom : NNG_LIBClaimsDomain.DomainClaims claims) (alphaDom : DomainArray alpha)
    (domain : LIB_VTerminal.Domain (pub,projectClaims fallback claims,projectArray fallback alpha,orig))
    (success : NNG_ModelTerminal.call (fromT9 pub) claims alpha (lowerChallenges orig) = .ok (.Ok q)) : Domain q := by
  let a : LIB_VTerminal.Args := (pub,projectClaims fallback claims,projectArray fallback alpha,orig)
  have lowered := NNG_LIBTerminal.native a
  dsimp only [a] at lowered
  rw [NNG_LIBClaimsDomain.lower_project fallback claims claimsDom,
    NNG_LIBArrayDomain.lower_project_array fallback alpha alphaDom] at lowered
  have whole := NNG_ModelTerminal.call_model (fromT9 pub) claims alpha (lowerChallenges orig)
  rw [success] at whole
  change Result.ok (core.result.Result.Ok (NNG_ModelTerminal.lowerQ q)) =
    NNG_ModelTerminal.native (fromT9 pub) claims alpha (lowerChallenges orig) at whole
  have native : LIB_VTerminal.native a = .ok (.Ok (NNG_ModelTerminal.lowerQ q)) := (whole.trans lowered).symm
  have good := LIB_VTerminal.native_good a domain
  rw [native] at good
  change Domain q at good
  exact good
#print axioms canonical
end AspisR1.NNG_TerminalReturned136
