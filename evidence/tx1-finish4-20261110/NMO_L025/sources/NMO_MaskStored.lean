import NMO_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_MaskStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def Canonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ value,s.locals.mask=some value→NKQ_MaskCuts.Canon value
theorem written {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.mask)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) : Canonical after := by
 obtain ⟨low,high,blind,alpha,lo,hi,bl,al,hl,hh,hb,ha⟩:=NMO_MaskAtState.arguments native cut token frame input domain s reached atSite
 obtain ⟨value,returned,canonical⟩:=NMO_MaskValue.source s.machine.input.reservation low high blind alpha hl hh hb ha
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let l ← NLC_Finish.read s.machine.locals.low
            let h ← NLC_Finish.read s.machine.locals.high
            let b ← NLC_Finish.read s.machine.locals.blind
            let a ← NLC_Finish.read s.machine.locals.alpha
            let v ← (IDa_Deployed.boundaries s.machine.input.reservation).mask l h b a
            ok (Sum.inr (NLC_Finish.put s.machine .record25a {s.machine.locals with mask:=some v}) : Post H))=ok (Sum.inr after : Post H) at actual
 rw [lo,hi,bl,al] at actual
 simp only [NLC_Finish.read,bind_tc_ok,returned] at actual
 have chosen:=Sum.inr.inj (Result.ok.inj actual)
 cases chosen
 intro v saved
 change some value=some v at saved
 cases Option.some.inj saved
 exact canonical
theorem preserved {H : Type} (s after : NLC_Finish.State H) (major : Major s)
 (before : Canonical s) (notMask : s.next≠.mask)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : Canonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro value stored
 rw [frame.2.2.2.2.2.2.2.2.2.1 notMask] at stored
 exact before value stored
theorem reachable {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) : Canonical s.machine := by
 induction reached with
 | initial=>intro value stored;cases stored
 | @next before after reached head ih=>
  have actual:=(NLU.next_characterization before after head).1
  by_cases atSite : before.machine.next=.mask
  · exact written native cut token frame input domain before reached atSite after.machine actual
  · exact preserved before.machine after.machine (NLU.reachable_invariant input before reached).1.2.1 ih atSite actual
#print axioms written
#print axioms preserved
#print axioms reachable
set_option pp.proofs false in #print reachable
end AspisR1.NMO_MaskStored
end
