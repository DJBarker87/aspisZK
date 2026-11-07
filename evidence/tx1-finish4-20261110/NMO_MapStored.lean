import NMO_TerminalStored
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_TerminalStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- The Public mapping copies exactly the successful canonical child value;
errors cannot enter the continuation. No independent value is supplied. -/
theorem map_written {H : Type} (s after : NLC_Finish.State H)
 (before : ReplyCanonical s) (atSite : s.next=.mapPublic)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : ValueCanonical after := by
 have actual : PreparedHashCode.erase (NLC_Finish.step s)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 cases slot : s.locals.terminalReply with
 | none=>rw [slot] at actual;cases actual
 | some result=>
  rw [slot] at actual
  cases result with
  | Err error=>cases actual
  | Ok value=>
   have chosen:=Sum.inr.inj (Result.ok.inj actual)
   cases chosen
   intro q stored
   change some value=some q at stored
   cases Option.some.inj stored
   exact before value slot
/-- Both invariants are derived along the ONE initialized source fold. The
native rounds cut is a reviewed child transcription, not a result premise. -/
theorem reachable {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) :
 ReplyCanonical s.machine ∧ ValueCanonical s.machine := by
 induction reached with
 | initial=>constructor <;> intro q stored <;> cases stored
 | @next before after reached head ih=>
  have actual:=(NLU.next_characterization before after head).1
  have major:=(NLU.reachable_invariant input before reached).1.2.1
  constructor
  · by_cases atTerminal : before.machine.next=.terminal
    · exact terminal_written native cut token frame input domain before reached atTerminal after.machine actual
    · exact reply_preserved before.machine after.machine major ih.1 atTerminal actual
  · by_cases atMap : before.machine.next=.mapPublic
    · exact map_written before.machine after.machine ih.1 atMap actual
    · exact value_preserved before.machine after.machine major ih.2 atMap actual
#print axioms map_written
#print axioms reachable
set_option pp.proofs false in #print reachable
end AspisR1.NMO_TerminalStored
end
