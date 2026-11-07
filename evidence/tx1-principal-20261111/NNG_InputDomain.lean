import NNG_InstallBase
import NNG_EmittedContext
import NLU_InputDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_InputDomain
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
/-- The SAME fresh inputs transported to the existing source occurrence fold.
Reservation is retained as data; it is never assumed successful. -/
def oldInput {H W : Type} (reservation : NP6_StdModel.Reservation) (s : Parent H W) : NLU.Input H :=
 ⟨reservation,NNG_Install.digest s.digest,toT9 s.publicValue,toT12 s.prefixValue,
  toT10 s.transcript,toT3 s.challenges⟩
/-- Only the three inherited own-input clauses. Neither Claims, alpha, a
record, a child Result nor the endpoint is supplied by the caller. -/
structure Domain {H W : Type} (s : Parent H W) : Prop where
 parsedPrefix : NLU.ParsedPrefix (toT12 s.prefixValue)
 terminal : NLU_Terminal.InputDomain (toT9 s.publicValue) (toT3 s.challenges)
 eta : JFv_RoundArithmetic.Canonical (toT3 s.challenges).eta
/-- Existing domain derivations apply to exactly this input, for every
reservation outcome. No new caller condition is introduced by the fresh copy. -/
theorem installed {H W : Type} (reservation : NP6_StdModel.Reservation) (s : Parent H W)
 (h : Domain s) : NLU.InputDomain (oldInput reservation s) :=
 ⟨h.parsedPrefix,h.terminal,h.eta⟩
#print axioms installed
end AspisR1.NNG_InputDomain
