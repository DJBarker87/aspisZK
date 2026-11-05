import NIG_LowLoop
import NIG_LoopPost
set_option autoImplicit false
namespace NIG_LowPost
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHX_LowDomain

theorem done (ap0 ap1:Powers) (s:State) (out:Cells)
 (hs:∀ x∈s.2.val,canonE x) (run:body ap0 ap1 s=ok (.done out)) :
 ∀ x∈out.val,canonE x := by
 unfold body FIo_Native.weights.Weights.pair_loop15.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>
  have same:=ControlFlow.done.inj (Result.ok.inj run)
  rw [←same]
  exact hs
 | some j=>
  obtain ⟨x0,h0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x1,h1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x2,h2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x3,h3,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x4,h4,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x5,h5,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x6,h6,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x7,h7,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x8,h8,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x9,h9,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run

theorem source (ap0 ap1:Powers) (ha:∀ x∈ap0.val,canonE x) (hb:∀ x∈ap1.val,canonE x)
 (cells out:Cells) (hc:∀ x∈cells.val,canonE x)
 (run:FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 cells=ok out) :
 ∀ x∈out.val,canonE x := by
 rw [NIG_LowLoop.low_source] at run
 exact NIG_LoopPost.post (body ap0 ap1) (fun s=>∀ x∈s.2.val,canonE x)
  (fun out=>∀ x∈out.val,canonE x)
  (fun s t hs step=>preserves ap0 ap1 ha hb s t hs step)
  (done ap0 ap1) 17 _ out hc run
#print axioms done
#print axioms source
end NIG_LowPost
