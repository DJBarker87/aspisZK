import NMC_TerminalAtState
import NMC_AllSlotFrames
import NLU_TerminalCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_TerminalStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Internal source invariant, never an additional root premise. -/
def ReplyCanonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ q,s.locals.terminalReply=some (.Ok q)→JFv_RoundArithmetic.Canonical q
def ValueCanonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ q,s.locals.terminal=some q→JFv_RoundArithmetic.Canonical q
/-- CLOSED256 canonicality is installed at the actual stored claims/alpha,
using the SAME reachable parent state and original own-argument domain. -/
theorem terminal_written {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.terminal)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) :
 ReplyCanonical after := by
 obtain ⟨claims,alpha,claimsStored,alphaStored,hc,ha,_⟩:=
  NMC_Terminal.actual_arguments native cut token frame input domain s reached atSite
 have inputEq:=(NLU.reachable_invariant input s reached).2
 have canonical:=NLU_Terminal.source input.reservation input.publicValue claims alpha input.challenges domain.terminal hc ha
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 rw [claimsStored,alphaStored] at actual
 change (do let result ← (IDa_Deployed.boundaries s.machine.input.reservation).terminal
             s.machine.input.publicValue claims alpha s.machine.input.challenges
            ok (.inr (NLC_Finish.put s.machine .mapPublic {s.machine.locals with terminalReply:=some result})))=ok (.inr after) at actual
 rw [inputEq] at actual
 cases child : (IDa_Deployed.boundaries input.reservation).terminal input.publicValue claims alpha input.challenges with
 | fail error=>rw [child] at actual;cases actual
 | div=>rw [child] at actual;cases actual
 | ok result=>
  simp only [child,bind_tc_ok] at actual
  have chosen:=Sum.inr.inj (Result.ok.inj actual)
  cases chosen
  intro q stored
  change some result=some (.Ok q) at stored
  cases Option.some.inj stored
  simpa only [child,NLU_Terminal.Outcome] using canonical
/-- Every nonwriter preserves the canonicality of the stored child reply. -/
theorem reply_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (before : ReplyCanonical s) (notTerminal : s.next≠.terminal)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : ReplyCanonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro q stored
 rw [frame.2.2.2.2.1 notTerminal] at stored
 exact before q stored
/-- Every nonwriter preserves the parent's terminal value. -/
theorem value_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (before : ValueCanonical s) (notMap : s.next≠.mapPublic)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : ValueCanonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro q stored
 rw [frame.2.2.2.2.2.1 notMap] at stored
 exact before q stored
#print axioms terminal_written
#print axioms reply_preserved
#print axioms value_preserved
set_option pp.proofs false in #print terminal_written
end AspisR1.NMO_TerminalStored
end
