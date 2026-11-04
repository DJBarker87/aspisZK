import NFM_Cuts
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFM_Frames
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input

theorem window (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (k : Fin 7) (limbs : NFM_Thread.Limbs) (cut : NFM_Cuts.Cut)
    (member : cut∈(NFM_Cuts.window oracle input k limbs).cuts) :
    cut.position=k ∧ cut.limbs=limbs ∧ cut.inner.input=input := by
  change cut∈((NFI_InnerTrace.run oracle
    ((NFA_Iterator.cursor ⟨k.val+1,by omega⟩).val-
     (NFA_Iterator.cursor ⟨k.val,by omega⟩).val)
    ⟨input,{start:=NFA_Iterator.cursor ⟨k.val,by omega⟩,
      «end»:=NFA_Iterator.cursor ⟨k.val+1,by omega⟩},Array.repeat 8#usize 0#u64⟩).2.map
    (fun inner => (⟨k,limbs,inner⟩ : NFM_Cuts.Cut))) at member
  obtain ⟨inner,visited,same⟩:=List.mem_map.mp member
  subst cut
  exact ⟨rfl,rfl,NFI_InnerTrace.frames oracle _ _ inner visited⟩

theorem sequence (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (positions : List (Fin 7)) (limbs : NFM_Thread.Limbs) (cut : NFM_Cuts.Cut)
    (member : cut∈(NFM_Cuts.sequence oracle input positions limbs).cuts) :
    cut.position∈positions ∧ cut.inner.input=input := by
  induction positions generalizing limbs with
  | nil => cases member
  | cons k rest ih =>
    have current (visited : cut∈(NFM_Cuts.window oracle input k limbs).cuts) :
        cut.position∈k::rest ∧ cut.inner.input=input := by
      have frame:=window oracle input k limbs cut visited
      exact ⟨List.mem_cons.mpr (Or.inl frame.1),frame.2.2⟩
    change cut∈(bindM (NFM_Cuts.window oracle input k limbs)
      (fun out => NFM_Cuts.sequence oracle input rest out)).cuts at member
    cases h : (NFM_Cuts.window oracle input k limbs).result with
    | fail e => simp only [bindM,h] at member; exact current member
    | div => simp only [bindM,h] at member; exact current member
    | ok out =>
      simp only [bindM,h,List.mem_append] at member
      rcases member with here | later
      · exact current here
      · have frame:=ih out later
        exact ⟨List.mem_cons.mpr (Or.inr frame.1),frame.2⟩

#print axioms window
#print axioms sequence
end AspisR1.NFM_Frames
end
