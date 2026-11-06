import NLU_StepProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Only continuation states: the original owner is absent up to claims,
then live until return/error. Dropped/transferred are terminal states. -/
def Linear {H : Type} (s : NLU.State H) : Prop :=
 if NLC_Finish.rank s.machine.next ≤ 2 then s.owner=.absent else s.owner=.live
theorem initial_linear {H : Type} (i : Input H) : Linear (initial i) := rfl
theorem claims_rank (e : NLC_Finish.Event) : NLC_Finish.rank e=2 ↔ e=.claims := by
 cases e <;> simp only [NLC_Finish.rank] <;> decide
theorem continuation_linear {H : Type} (s : NLU.State H) (after : NLC_Finish.State H)
 (before : Linear s)
 (head : (PreparedHashCode.run (NLC_Finish.step s.machine)).2=.ok (.inr after)) :
 Linear (⟨after,carryOwner s⟩ : NLU.State H) := by
 have order := NLC_Finish.source_progress s.machine after head
 by_cases atClaims : s.machine.next=.claims
 · have r : NLC_Finish.rank s.machine.next=2 := (claims_rank _).mpr atClaims
   have later : ¬ NLC_Finish.rank after.next≤2 := by omega
   simp only [Linear,later,ite_false,carryOwner,atClaims,ite_true]
 · have different : NLC_Finish.rank s.machine.next≠2 := by
     intro h;exact atClaims ((claims_rank _).mp h)
   unfold Linear at before ⊢
   simp only [carryOwner,atClaims,ite_false]
   by_cases early : NLC_Finish.rank s.machine.next≤2
   · have nextEarly : NLC_Finish.rank after.next≤2 := by omega
     simpa only [early,nextEarly,ite_true] using before
   · have nextLate : ¬ NLC_Finish.rank after.next≤2 := by omega
     simpa only [early,nextLate,ite_false] using before
#print axioms initial_linear
#print axioms claims_rank
#print axioms continuation_linear
end AspisR1.NLU
end
