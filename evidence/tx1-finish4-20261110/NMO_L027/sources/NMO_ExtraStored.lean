import NMO_ExtraValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ExtraStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def Canonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ value,s.locals.extra=some value→NMO_ExtraValue.Canonical value
theorem written {H : Type} (input : NLU.Input H) (s : NLU.State H)
 (reached : NLU.Reachable input s) (atSite : s.machine.next=.decode25)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) : Canonical after := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨record,stored⟩:=NMC_Records.some_slot s.machine.locals.record25 initialized
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let r ← NLC_Finish.read s.machine.locals.record25
            let result ← NJM_RoundJoin.R.decode 29#usize r 87#usize
            ok (NLC_Finish.returned s.machine .multiply result (fun value=>{s.machine.locals with extra:=some value})))=ok (Sum.inr after : Post H) at actual
 rw [stored] at actual
 simp only [NLC_Finish.read,bind_tc_ok] at actual
 cases child : NJM_RoundJoin.R.decode 29#usize record 87#usize with
 | fail error=>rw [child] at actual;cases actual
 | div=>rw [child] at actual;cases actual
 | ok result=>
  cases result with
  | Err error=>simp only [child,bind_tc_ok,NLC_Finish.returned] at actual;cases actual
  | Ok value=>
   simp only [child,bind_tc_ok,NLC_Finish.returned] at actual
   have chosen:=Sum.inr.inj (Result.ok.inj actual)
   cases chosen
   intro words saved
   change some value=some words at saved
   cases Option.some.inj saved
   exact NMO_ExtraValue.decoded record 87#usize value child
theorem preserved {H : Type} (s after : NLC_Finish.State H) (major : Major s)
 (before : Canonical s) (notDecode : s.next≠.decode25)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : Canonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro value stored
 rw [frame.2.2.2.2.2.2.2.2.2.2.1 notDecode] at stored
 exact before value stored
theorem reachable {H : Type} (input : NLU.Input H) (s : NLU.State H)
 (reached : NLU.Reachable input s) : Canonical s.machine := by
 induction reached with
 | initial=>intro value stored;cases stored
 | @next before after reached head ih=>
  have actual:=(NLU.next_characterization before after head).1
  by_cases atSite : before.machine.next=.decode25
  · exact written input before reached atSite after.machine actual
  · exact preserved before.machine after.machine (NLU.reachable_invariant input before reached).1.2.1 ih atSite actual
#print axioms written
#print axioms preserved
#print axioms reachable
end AspisR1.NMO_ExtraStored
end
