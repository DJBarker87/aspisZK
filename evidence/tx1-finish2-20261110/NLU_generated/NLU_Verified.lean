import NLU_Invariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
theorem some_of_initialized {A : Type} (slot : Option A) (h : slot.isSome=true) :
 ∃ value,slot=some value := by
 cases slot with
 | none=>cases h
 | some value=>exact ⟨value,rfl⟩
/-- The final constructor is produced from THIS initialized parent's fields.
No successful Verified, independent claims owner or terminal endpoint enters
as a premise. Native constructor-window association is still separate. -/
theorem verified_constructed {H : Type} (input : Input H) (s : NLU.State H)
 (reached : Reachable input s) (atSite : s.machine.next=.verified) :
 ∃ verified : r1_semantic.Verified H,
 (step s).reply=ok (.inl (.Ok verified,.transferred)) ∧
 s.machine.locals.claims=some verified.claims ∧
 verified.challenges=input.challenges ∧ s.owner=.live := by
 have inv:=(reachable_invariant input s reached).1
 have frame:=(reachable_invariant input s reached).2
 have ready:=NLC_Finish.ready_reads s.machine inv.1
 simp only [NLC_Finish.ReadsReady,atSite] at ready
 rcases ready with ⟨hr,ha,hc,he,hb,hs,h0,h1,ht⟩
 obtain ⟨root,er⟩:=some_of_initialized _ hr
 obtain ⟨alpha,ea⟩:=some_of_initialized _ ha
 obtain ⟨claims,ec⟩:=some_of_initialized _ hc
 obtain ⟨extra,ee⟩:=some_of_initialized _ he
 obtain ⟨beforeZ1,eb⟩:=some_of_initialized _ hb
 obtain ⟨stateBefore,es⟩:=some_of_initialized _ hs
 obtain ⟨z0,e0⟩:=some_of_initialized _ h0
 obtain ⟨z1,e1⟩:=some_of_initialized _ h1
 obtain ⟨transcript,et⟩:=some_of_initialized _ ht
 have live:=inv.2.2
 simp only [Linear,atSite,NLC_Finish.rank,show ¬ (31:Nat)≤2 by decide,ite_false] at live
 let value : r1_semantic.Verified H := {
  roots:=Array.make 2#usize [s.machine.input.prefix1.c1_root,root],
  challenges:=s.machine.input.challenges,alpha:=alpha,claims:=claims,
  extra:=extra,before_z1:=beforeZ1,state_before_z0:=stateBefore,
  z:=Array.make 2#usize [z0,z1],transcript:=transcript}
 refine ⟨value,?_,ec,?_,live⟩
 · unfold step
   simp only [NLC_Finish.step,atSite,er,ea,ec,ee,eb,es,e0,e1,et,NLC_Finish.read]
   rfl
 · change s.machine.input.challenges=input.challenges
   rw [frame]
#print axioms some_of_initialized
#print axioms verified_constructed
set_option pp.proofs false in #print verified_constructed
end AspisR1.NLU
end
