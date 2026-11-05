import NHM_GroupCoefficient
import NHM_LoopDomain
set_option autoImplicit false
namespace NHM_GroupCoefficientDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_GroupCoefficient

def Inv (s : State) : Prop := s.1.end.val=64 ∧ s.1.start.val≤64 ∧ ∀ x∈s.2.val,canonE x

theorem preserves (f : Slice U8) (s t : State) (h : Inv s)
 (run : body f s=ok (.cont t)) : Inv t := by
 rcases h with ⟨last,bound,canon⟩
 have ⟨he,hi,active⟩:=progress f s t run
 have hev:=congrArg (fun x : Usize=>x.val) he
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  have index:=(NHI_RangeProgress.some_next s.1 next j hn).1
  have small : j.val<64 := by rw [index];omega
  have after:=canonical f j s.2 out small canon ho
  unfold Inv
  refine ⟨by omega,by omega,?_⟩
  rw [←same]
  exact after

theorem terminal (f : Slice U8) (s : State) (out : Cells) (h : Inv s)
 (run : body f s=ok (.done out)) : ∀ x∈out.val,canonE x := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases ControlFlow.done.inj (Result.ok.inj run);exact h.2.2
 | some j=>
  obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases run

theorem result (f : Slice U8) (before out : Cells) (hc : ∀ x∈before.val,canonE x)
 (run : FIo_Native.weights.s2_grouped_inactive_pair_loop0
  {start:=0#usize,«end»:=64#usize} f before=ok out) : ∀ x∈out.val,canonE x := by
 rw [source] at run
 exact NHM_ResultInvariant.stateful (body f) Inv (fun a=>∀ x∈a.val,canonE x)
  (preserves f) (terminal f) 65 _ out ⟨rfl,by change (0:Nat)≤64;omega,hc⟩ run

#print axioms preserves
#print axioms terminal
#print axioms result
end NHM_GroupCoefficientDomain
