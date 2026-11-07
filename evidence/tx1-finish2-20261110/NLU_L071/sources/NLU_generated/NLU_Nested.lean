import NLU_Execute
import NLU_Invariant
import NLC_Suboccurrences
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Low callback arguments are read from THIS reachable parent. The bound is
internal to from_fn, not a136 caller clause. This is source support only. -/
theorem low_arguments {H : Type} (input : Input H) (s : NLU.State H)
 (reached : Reachable input s) (atSite : s.machine.next=.lowArray) :
 ∃ claims,s.machine.locals.claims=some claims ∧ s.owner=.live ∧
 ∀ (i : Usize) (inside : i.val<16),
 (do let c ← NLC_Finish.read s.machine.locals.claims
     (FinishModel.closureFn9 s.machine.input.digest).call_mut c i)=
 ok (NKQ_MaskLowStep.lowAt claims i inside,claims) := by
 have inv:=(reachable_invariant input s reached).1
 have initialized:=NLC_Finish.ready_reads s.machine inv.1
 change NLC_Finish.ReadsReady s.machine at initialized
 simp only [NLC_Finish.ReadsReady,atSite] at initialized
 have live:=inv.2.2
 simp only [Linear,atSite,NLC_Finish.rank,show ¬ (7:Nat)≤2 by decide,ite_false] at live
 cases slot : s.machine.locals.claims with
 | none => rw [slot] at initialized;cases initialized
 | some claims =>
   refine ⟨claims,slot,live,?_⟩
   intro i hi
   exact NLC_Finish.low_callback s.machine claims slot i hi
/-- High callback uses the same retained Claims owner and the actual16+i
offset, without a completed destination array as a hypothesis. -/
theorem high_arguments {H : Type} (input : Input H) (s : NLU.State H)
 (reached : Reachable input s) (atSite : s.machine.next=.highArray) :
 ∃ claims,s.machine.locals.claims=some claims ∧ s.owner=.live ∧
 ∀ (i : Usize) (inside : i.val<10),
 (do let c ← NLC_Finish.read s.machine.locals.claims
     (FinishModel.closureFn5 s.machine.input.digest).call_mut c i)=
 ok (NKQ_MaskHighStep.highAt claims i inside,claims) := by
 have inv:=(reachable_invariant input s reached).1
 have initialized:=NLC_Finish.ready_reads s.machine inv.1
 simp only [NLC_Finish.ReadsReady,atSite] at initialized
 have live:=inv.2.2
 simp only [Linear,atSite,NLC_Finish.rank,show ¬ (8:Nat)≤2 by decide,ite_false] at live
 cases slot : s.machine.locals.claims with
 | none => rw [slot] at initialized;cases initialized
 | some claims =>
   refine ⟨claims,slot,live,?_⟩
   intro i hi
   exact NLC_Finish.high_callback s.machine claims slot i hi
/-- try_into precedes unwrap in the SAME rootCopy state; outer abort never
runs a fabricated suffix. NLC's emitted-body split is reused verbatim. -/
theorem root_occurrences {H : Type} (s : NLU.State H) (atSite : s.machine.next=.rootCopy) :
 step s=execute s (do let attempted ← NLC_Finish.rootTry s.machine
                      NLC_Finish.rootUnwrap s.machine attempted) := by
 rw [execute_step,NLC_Finish.root_occurrences s.machine atSite]
#print axioms low_arguments
#print axioms high_arguments
#print axioms root_occurrences
end AspisR1.NLU
end
