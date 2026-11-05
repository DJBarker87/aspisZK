import NHM_GroupAccum
set_option autoImplicit false
namespace NHM_GroupAccumDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_GroupAccum

theorem preserves (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (cells : Cells) (hc : ∀ x∈cells.val,canonE x) (s t : State) (hp : canonE s.2)
 (run : body low cells s=ok (.cont t)) : canonE t.2 := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some group=>
  obtain ⟨weight,hw,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have cw:=NHM_GroupWeightDomain.result low hl group NHI_Scalar.zero weight NHI_Scalar.zero_canonical hw
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact canonical cells hc group weight s.2 out cw hp ho

theorem terminal (low : Array NE 16#usize) (cells : Cells) (s : State) (out : NE)
 (hc : canonE s.2) (run : body low cells s=ok (.done out)) : canonE out := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases ControlFlow.done.inj (Result.ok.inj run);exact hc
 | some group=>
  obtain ⟨weight,hw,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases run

theorem result (low : Array NE 16#usize) (hl : ∀ x∈low.val,canonE x)
 (cells : Cells) (hc : ∀ x∈cells.val,canonE x) (before out : NE) (hp : canonE before)
 (run : reference low cells before=ok out) : canonE out :=
 NHM_ResultInvariant.stateful (body low cells) (fun s=>canonE s.2) canonE
  (preserves low hl cells hc) (terminal low cells) 13 _ out hp run

#print axioms preserves
#print axioms terminal
#print axioms result
end NHM_GroupAccumDomain
