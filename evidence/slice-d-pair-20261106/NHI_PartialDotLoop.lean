import NHI_CountedLoop
import NHI_RangeProgress
import NHI_PartialIndex
import NHE_DotDomain
set_option autoImplicit false
namespace NHI_PartialDotLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev Dot := NHE_DotState.Dot
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × Dot
abbrev NQ := NHE_CheckedScalar.NQ
abbrev NE := FIo_Install.NE
abbrev body (f : Slice U8) (scratch : Array NQ 16#usize) (offset : Usize) (s : State) :=
 FIo_Native.weights.partial_dot_loop.body f scratch offset s.1 s.2

theorem progress (f : Slice U8) (scratch : Array NQ 16#usize) (offset : Usize) (s t : State)
 (run : body f scratch offset s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧
 t.2.count.val=s.2.count.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body FIo_Native.weights.partial_dot_loop.body at run
 obtain ⟨⟨o,rest⟩,next,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none =>
  obtain ⟨out,hout,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases run
 | some j =>
  simp only [lift,bind_tc_ok] at run
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

theorem decreases (f : Slice U8) (scratch : Array NQ 16#usize) (offset : Usize) (s t : State)
 (run : body f scratch offset s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,count,more⟩ := progress f scratch offset s t run
 rw [last]
 omega

/-- Exact sixteen-window wrapper, retaining finish and every error prefix. -/
theorem source (f : Slice U8) (scratch : Array NQ 16#usize) (offset : Usize) :
 FIo_Native.weights.partial_dot f scratch offset=
 (do let pair ← FIo_Native.fast_pairing.EbyKDot.new
     NHI_CountedLoop.unroll (body f scratch offset) 17 ({start:=0#usize,«end»:=16#usize},pair)) := by
 unfold FIo_Native.weights.partial_dot FIo_Native.weights.partial_dot_loop
 congr 1
 funext pair
 exact NHI_CountedLoop.agrees (body f scratch offset) (fun s=>s.1.end.val-s.1.start.val)
  (decreases f scratch offset) 17 _ (by change (16:Nat)-0<17;omega)

#print axioms progress
#print axioms decreases
#print axioms source
end NHI_PartialDotLoop
