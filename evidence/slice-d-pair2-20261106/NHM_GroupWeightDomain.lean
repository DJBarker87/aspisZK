import NHM_GroupWeight
set_option autoImplicit false
namespace NHM_GroupWeightDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_GroupWeight

theorem preserves (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (group : Usize) (s t : State) (hc : canonE s.2)
 (run : body low group s=ok (.cont t)) : canonE t.2 := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some bit=>
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact canonical low hl group bit s.2 out hc ho

theorem terminal (low : Array NE 16#usize) (group : Usize) (s : State) (out : NE)
 (hc : canonE s.2) (run : body low group s=ok (.done out)) : canonE out := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases ControlFlow.done.inj (Result.ok.inj run);exact hc
 | some bit=>
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases run

theorem result (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (group : Usize) (before out : NE) (hc : canonE before)
 (run : reference low group before=ok out) : canonE out :=
 NHM_ResultInvariant.stateful (body low group) (fun s=>canonE s.2) canonE
  (preserves low hl group) (terminal low group) 17 _ out hc run

#print axioms preserves
#print axioms terminal
#print axioms result
end NHM_GroupWeightDomain
