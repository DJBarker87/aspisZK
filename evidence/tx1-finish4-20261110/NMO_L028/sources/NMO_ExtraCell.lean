import NMO_ExtraStored
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ExtraCell
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def Canonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ value,s.locals.extraCell=some value→JFv_RoundArithmetic.Canonical value
theorem written {H : Type} (input : NLU.Input H) (s : NLU.State H)
 (reached : NLU.Reachable input s) (atSite : s.machine.next=.extra28)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) : Canonical after := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨words,stored⟩:=NMC_Records.some_slot s.machine.locals.extra initialized
 have canonical:=(NMO_ExtraStored.reachable input s reached) words stored
 have value:=NKQ_ArrayWindows.read words 28#usize (by decide)
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let a ← NLC_Finish.read s.machine.locals.extra
            let v ← Array.index_usize a 28#usize
            ok (Sum.inr (NLC_Finish.put s.machine .addExtra {s.machine.locals with extraCell:=some v}) : Post H))=ok (Sum.inr after : Post H) at actual
 rw [stored] at actual
 simp only [NLC_Finish.read,bind_tc_ok,value] at actual
 have chosen:=Sum.inr.inj (Result.ok.inj actual)
 cases chosen
 intro v saved
 change some (NKQ_ArrayWindows.cell words 28 (by decide))=some v at saved
 cases Option.some.inj saved
 exact canonical _ (List.getElem_mem _)
theorem preserved {H : Type} (s after : NLC_Finish.State H) (major : Major s)
 (before : Canonical s) (notExtra : s.next≠.extra28)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : Canonical after := by
 have frame:=NMC_Slots.source_frame s after major head
 intro value stored
 rw [frame.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 notExtra] at stored
 exact before value stored
theorem reachable {H : Type} (input : NLU.Input H) (s : NLU.State H)
 (reached : NLU.Reachable input s) : Canonical s.machine := by
 induction reached with
 | initial=>intro value stored;cases stored
 | @next before after reached head ih=>
  have actual:=(NLU.next_characterization before after head).1
  by_cases atSite : before.machine.next=.extra28
  · exact written input before reached atSite after.machine actual
  · exact preserved before.machine after.machine (NLU.reachable_invariant input before reached).1.2.1 ih atSite actual
#print axioms written
#print axioms preserved
#print axioms reachable
end AspisR1.NMO_ExtraCell
end
