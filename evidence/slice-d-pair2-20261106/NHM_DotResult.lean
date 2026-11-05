import NHM_HighDot
import NHM_PartialDot
import NHM_DotFinishCanonical
import NHM_DotInitial
import NHM_ResultInvariant
set_option autoImplicit false
namespace NHM_DotResult
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues

theorem high_terminal (p : Array NE 4#usize) (q : Array NQ 4#usize)
 (s : NHM_HighDot.State) (x : NE)
 (run : NHM_HighDot.body p q s=ok (.done (.Ok x))) : canonE x := by
 unfold NHM_HighDot.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>
  obtain ⟨out,ho,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same:=core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj run))
  subst out
  exact NHM_DotFinishCanonical.source s.2 x ho
 | some j=>
  obtain ⟨value,hv,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨scalar,hs,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨reply,after⟩,hp,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases reply with
  | Ok u=>cases run
  | Err u=>cases run

theorem partial_terminal (f : Slice U8) (q : Array NQ 16#usize) (offset : Usize)
 (s : NHM_PartialDot.State) (x : NE)
 (run : NHM_PartialDot.body f q offset s=ok (.done (.Ok x))) : canonE x := by
 unfold NHM_PartialDot.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>
  obtain ⟨out,ho,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same:=core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj run))
  subst out
  exact NHM_DotFinishCanonical.source s.2 x ho
 | some j=>
  obtain ⟨value,hv,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨scalar,hs,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨reply,after⟩,hp,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases reply with
  | Ok u=>cases run
  | Err u=>cases run

def canonicalResult : core.result.Result NE FIo_Native.verifier.Error→Prop
 | .Ok x=>canonE x
 | .Err _=>True

theorem high (p : Array NE 4#usize) (q : Array NQ 4#usize) (x : NE)
 (run : FIo_Native.weights.high_dot p q=ok (.Ok x)) : canonE x := by
 rw [NHM_HighDot.cohort] at run
 unfold NHM_HighDot.reference at run
 rw [NHM_DotInitial.source] at run
 simp only [bind_tc_ok] at run
 apply NHM_ResultInvariant.terminal (NHM_HighDot.body p q) canonicalResult _ 5 _ (.Ok x) run
 intro s r hr
 cases r with
 | Err e=>trivial
 | Ok y=>exact high_terminal p q s y hr

theorem partial_result (f : Slice U8) (q : Array NQ 16#usize) (offset : Usize) (x : NE)
 (run : FIo_Native.weights.partial_dot f q offset=ok (.Ok x)) : canonE x := by
 rw [NHM_PartialDot.cohort] at run
 unfold NHM_PartialDot.reference at run
 rw [NHM_DotInitial.source] at run
 simp only [bind_tc_ok] at run
 apply NHM_ResultInvariant.terminal (NHM_PartialDot.body f q offset) canonicalResult _ 17 _ (.Ok x) run
 intro s r hr
 cases r with
 | Err e=>trivial
 | Ok y=>exact partial_terminal f q offset s y hr

#print axioms high_terminal
#print axioms partial_terminal
#print axioms high
#print axioms partial_result
end NHM_DotResult
