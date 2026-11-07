import NMC_RecordPreserved
import NLU_DecodeDomains
import NLU_CircleDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Records
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem unique {T E : Type} (reply : Result (core.result.Result T E)) (a b : T)
 (left : reply=ok (.Ok a)) (right : reply=ok (.Ok b)) : a=b :=
 core.result.Result.Ok.inj (Result.ok.inj (left.symm.trans right))
/-- Actual record25 at the decode87 occurrence, from the SAME current Prefix. -/
theorem decode25 {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.decode25) :
 ∃ record,s.machine.locals.record25=some record ∧ NKQ_RecordDomains.Ready record 29#usize 87#usize := by
 have inv:=NLU.reachable_invariant input s reached
 have initialized:=NLC_Finish.ready_reads s.machine inv.1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨record,stored⟩:=some_slot s.machine.locals.record25 initialized
 have current:=(reachable input s reached).1 record stored
 rw [inv.2] at current
 obtain ⟨first,second,firstCall,secondCall,_,_,firstReady,_⟩:=NLU_Decode.source input domain
 have same:=unique _ record first current firstCall
 cases same
 exact ⟨record,stored,firstReady⟩
theorem decode26 {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.decode26) :
 ∃ record,s.machine.locals.record26=some record ∧ NKQ_RecordDomains.Ready record 29#usize 0#usize := by
 have inv:=NLU.reachable_invariant input s reached
 have initialized:=NLC_Finish.ready_reads s.machine inv.1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨record,stored⟩:=some_slot s.machine.locals.record26 initialized
 have current:=(reachable input s reached).2 record stored
 rw [inv.2] at current
 obtain ⟨first,second,firstCall,secondCall,_,_,_,secondReady⟩:=NLU_Decode.source input domain
 have same:=unique _ record second current secondCall
 cases same
 exact ⟨record,stored,secondReady⟩
/-- Circle142 is instantiated at the ACTUAL current transcript slot, not an
independently selected earlier successful carry. The other circle's unused
argument in the generic domain lemma is irrelevant to this entered site. -/
theorem circle0 {Pointer H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.circle0)
 (template : NIX_DispatchCut.Pre Pointer) :
 ∃ record transcript,s.machine.locals.record25=some record ∧ s.machine.locals.transcript=some transcript ∧
 NJM_InvocationRoots.Circle input.digest template transcript record := by
 have inv:=NLU.reachable_invariant input s reached
 have initialized:=NLC_Finish.ready_reads s.machine inv.1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨transcript,storedT⟩:=some_slot s.machine.locals.transcript initialized.1
 obtain ⟨record,stored⟩:=some_slot s.machine.locals.record25 initialized.2
 have current:=(reachable input s reached).1 record stored
 rw [inv.2] at current
 obtain ⟨first,second,firstCall,secondCall,_,_,firstDomain,_⟩:=NLU_Circle.source input domain template transcript transcript
 have same:=unique _ record first current firstCall
 cases same
 exact ⟨record,transcript,stored,storedT,firstDomain⟩
theorem circle1 {Pointer H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.circle1)
 (template : NIX_DispatchCut.Pre Pointer) :
 ∃ record transcript,s.machine.locals.record26=some record ∧ s.machine.locals.transcript=some transcript ∧
 NJM_InvocationRoots.Circle input.digest template transcript record := by
 have inv:=NLU.reachable_invariant input s reached
 have initialized:=NLC_Finish.ready_reads s.machine inv.1.1
 simp only [ReadsReady,atSite] at initialized
 obtain ⟨transcript,storedT⟩:=some_slot s.machine.locals.transcript initialized.1
 obtain ⟨record,stored⟩:=some_slot s.machine.locals.record26 initialized.2
 have current:=(reachable input s reached).2 record stored
 rw [inv.2] at current
 obtain ⟨first,second,firstCall,secondCall,_,_,_,secondDomain⟩:=NLU_Circle.source input domain template transcript transcript
 have same:=unique _ record second current secondCall
 cases same
 exact ⟨record,transcript,stored,storedT,secondDomain⟩
#print axioms unique
#print axioms decode25
#print axioms decode26
#print axioms circle0
#print axioms circle1
set_option pp.proofs false in #print decode25
set_option pp.proofs false in #print decode26
set_option pp.proofs false in #print circle0
set_option pp.proofs false in #print circle1
end AspisR1.NMC_Records
end
