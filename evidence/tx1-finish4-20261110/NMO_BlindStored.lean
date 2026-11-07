import NMO_ArrayStored
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ArrayStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def BlindCanonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ value,s.locals.blind=some value→NKQ_MaskCuts.Canon value
/-- Blind is precisely the canonical cell 27 of the actual stored Claims. -/
theorem blind_written {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.blind)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) : BlindCanonical after := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨claims,stored⟩:=NMC_Records.some_slot s.machine.locals.claims initialized
 have canonical:=NKQ_MaskCanonical.claim_cell claims (NMO_ClaimsAtState.claims input domain s reached claims stored) 0 27 (by decide) (by decide)
 have row:=NKQ_ArrayWindows.read claims 0#usize (by decide)
 have value:=NKQ_ArrayWindows.read (NKQ_ArrayWindows.cell claims (0#usize).val (by decide)) 27#usize (by decide)
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let c ← NLC_Finish.read s.machine.locals.claims
            let r ← Array.index_usize c 0#usize
            let b ← Array.index_usize r 27#usize
            ok (Sum.inr (NLC_Finish.put s.machine .alpha {s.machine.locals with blind:=some b}) : Post H))=ok (Sum.inr after : Post H) at actual
 rw [stored] at actual
 simp only [NLC_Finish.read,bind_tc_ok,row] at actual
 rw [value] at actual
 simp only [bind_tc_ok] at actual
 have chosen:=Sum.inr.inj (Result.ok.inj actual)
 cases chosen
 intro b saved
 change some (NKQ_ArrayWindows.cell (NKQ_ArrayWindows.cell claims 0 (by decide)) 27 (by decide))=some b at saved
 cases Option.some.inj saved
 exact canonical
#print axioms blind_written
end AspisR1.NMO_ArrayStored
end
