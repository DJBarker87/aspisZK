import NHI_CountedLoop
import NHI_RangeProgress
import NHE_DotDomain
set_option autoImplicit false
namespace NHI_HighDotLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev Dot := NHE_DotState.Dot
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × Dot
abbrev NQ := NHE_CheckedScalar.NQ
abbrev NE := FIo_Install.NE
abbrev body (f : Array NE 4#usize) (scratch : Array NQ 4#usize) (s : State) :=
 FIo_Native.weights.high_dot_loop.body f scratch s.1 s.2

theorem progress (f : Array NE 4#usize) (scratch : Array NQ 4#usize) (s t : State)
 (run : body f scratch s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧
 t.2.count.val=s.2.count.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body FIo_Native.weights.high_dot_loop.body at run
 obtain ⟨⟨o,rest⟩,next,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none =>
  obtain ⟨out,hout,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases run
 | some j =>
  obtain ⟨value,hv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨scalar,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r,after⟩,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok u =>
   cases u
   have same := ControlFlow.cont.inj (Result.ok.inj run)
   rw [←same]
   have index := NHI_RangeProgress.some_next s.1 rest j next
   exact ⟨index.2.1,index.2.2.1,NHE_DotDomain.push_count s.2 after value scalar hp,index.2.2.2⟩

theorem decreases (f : Array NE 4#usize) (scratch : Array NQ 4#usize) (s t : State)
 (run : body f scratch s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,count,more⟩ := progress f scratch s t run
 rw [last]
 omega

/-- Exact four-call wrapper, retaining finish and every error prefix. -/
theorem source (f : Array NE 4#usize) (scratch : Array NQ 4#usize) :
 FIo_Native.weights.high_dot f scratch=
 (do let pair ← FIo_Native.fast_pairing.EbyKDot.new
     NHI_CountedLoop.unroll (body f scratch) 5 ({start:=0#usize,«end»:=4#usize},pair)) := by
 unfold FIo_Native.weights.high_dot FIo_Native.weights.high_dot_loop
 congr 1
 funext pair
 exact NHI_CountedLoop.agrees (body f scratch) (fun s=>s.1.end.val-s.1.start.val)
  (decreases f scratch) 5 _ (by change (4:Nat)-0<5;omega)

#print axioms progress
#print axioms decreases
#print axioms source
end NHI_HighDotLoop
