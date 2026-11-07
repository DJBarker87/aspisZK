import NMO_ClaimsAtState
import NMC_AllSlotFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ArrayStored
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def LowCanonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ value,s.locals.low=some value→∀ q∈value.val,NKQ_MaskCuts.Canon q
/-- Exact source array producer, canonical at the actual stored Claims. -/
theorem low_written {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.lowArray)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) : LowCanonical after := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨claims,stored⟩:=NMC_Records.some_slot s.machine.locals.claims initialized
 have canonical:=NKQ_MaskCanonical.low claims (NMO_ClaimsAtState.claims input domain s reached claims stored)
 have producer:=NKQ_MaskArrays.low_source s.machine.input.reservation s.machine.input.digest claims
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let c ← NLC_Finish.read s.machine.locals.claims
            let value ← (IDa_Deployed.boundaries s.machine.input.reservation).fromFn 16#usize (FinishModel.closureFn9 s.machine.input.digest) c
            ok (Sum.inr (NLC_Finish.put s.machine .highArray {s.machine.locals with low:=some value}) : Post H))=ok (Sum.inr after : Post H) at actual
 rw [stored] at actual
 simp only [NLC_Finish.read,bind_tc_ok,producer] at actual
 have chosen:=Sum.inr.inj (Result.ok.inj actual)
 cases chosen
 intro value saved
 change some (NKQ_MaskArrays.lowArray claims)=some value at saved
 cases Option.some.inj saved
 exact canonical
#print axioms low_written
def HighCanonical {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ value,s.locals.high=some value→∀ q∈value.val,NKQ_MaskCuts.Canon q
/-- Exact source array producer, canonical at the actual stored Claims. -/
theorem high_written {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.highArray)
 (after : NLC_Finish.State H)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=ok (.inr after)) : HighCanonical after := by
 have initialized:=NLC_Finish.ready_reads s.machine (NLU.reachable_invariant input s reached).1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨claims,stored⟩:=NMC_Records.some_slot s.machine.locals.claims initialized
 have canonical:=NKQ_MaskCanonical.high claims (NMO_ClaimsAtState.claims input domain s reached claims stored)
 have producer:=NKQ_MaskArrays.high_source s.machine.input.reservation s.machine.input.digest claims
 have actual : PreparedHashCode.erase (NLC_Finish.step s.machine)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 simp only [NLC_Finish.step,atSite] at actual
 change (do let c ← NLC_Finish.read s.machine.locals.claims
            let value ← (IDa_Deployed.boundaries s.machine.input.reservation).fromFn 10#usize (FinishModel.closureFn5 s.machine.input.digest) c
            ok (Sum.inr (NLC_Finish.put s.machine .blind {s.machine.locals with high:=some value}) : Post H))=ok (Sum.inr after : Post H) at actual
 rw [stored] at actual
 simp only [NLC_Finish.read,bind_tc_ok,producer] at actual
 have chosen:=Sum.inr.inj (Result.ok.inj actual)
 cases chosen
 intro value saved
 change some (NKQ_MaskArrays.highArray claims)=some value at saved
 cases Option.some.inj saved
 exact canonical
#print axioms high_written
end AspisR1.NMO_ArrayStored
end
