import NMC_OriginWrites
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Origins
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Both stored arrays retain the SAME original child-call provenance through
all source occurrences. No independent successful output is supplied. -/
theorem reachable {H : Type} (input : NLU.Input H) (s : NLU.State H)
 (reached : NLU.Reachable input s) : ClaimsOrigin s.machine ∧ AlphaOrigin s.machine := by
 induction reached with
 | initial=>exact ⟨initial_claims input,initial_alpha input⟩
 | @next before after reached head ih=>
   have actual:=(NLU.next_characterization before after head).1
   have major:=(NLU.reachable_invariant input before reached).1.2.1
   constructor
   · by_cases atClaims : before.machine.next=.claims
     · exact claims_written before.machine after.machine atClaims actual
     · exact claims_preserved before.machine after.machine major ih.1 atClaims actual
   · by_cases atRounds : before.machine.next=.rounds
     · exact alpha_written before.machine after.machine atRounds actual
     · exact alpha_preserved before.machine after.machine major ih.2 atRounds actual
#print axioms reachable
set_option pp.proofs false in #print reachable
end AspisR1.NMC_Origins
end
