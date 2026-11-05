import NHM_ControlExtracted
import NHI_CountedLoop
import NHI_RangeProgress
set_option autoImplicit false
namespace NHM_ControlLoop
open Aeneas Aeneas.Std Result ControlFlow
abbrev State := NHI_RangeProgress.Range × Usize
abbrev body (stop : Usize) (s : State) := NHM_ControlRef.control_ref_loop.body stop s.1 s.2

theorem progress (stop : Usize) (s t : State) (run : body stop s=ok (ControlFlow.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body NHM_ControlRef.control_ref_loop.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  simp only [lift,bind_tc_ok] at run
  change (if j=stop then ok (ControlFlow.done (s.2.wrapping_add 1#usize,
   some (core.result.Result.Err NHM_ControlRef.NHM_ControlError.Parse,s.2.wrapping_add 1#usize)))
   else ok (ControlFlow.cont (next,s.2.wrapping_add 1#usize)))=ok (ControlFlow.cont t) at run
  split at run
  · cases run
  · have same:=ControlFlow.cont.inj (Result.ok.inj run)
    rw [←same]
    exact (NHI_RangeProgress.some_next s.1 next j hn).2

theorem decreases (stop : Usize) (s t : State) (run : body stop s=ok (ControlFlow.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,active⟩ := progress stop s t run
 have value:=congrArg (fun x : Usize=>x.val) last
 omega

def reference (n stop : Usize) := do
 let (calls,pending) ← NHI_CountedLoop.unroll (body stop) (n.val+1)
  ({start:=0#usize,«end»:=n},0#usize)
 match pending with
 | none=>ok (core.result.Result.Ok (),calls)
 | some reply=>ok reply

theorem source (n stop : Usize) : NHM_ControlRef.control_ref n stop=reference n stop := by
 unfold NHM_ControlRef.control_ref NHM_ControlRef.control_ref_loop reference
 have eqn := NHI_CountedLoop.agrees (body stop) (fun s=>s.1.end.val-s.1.start.val)
  (decreases stop) (n.val+1) ({start:=0#usize,«end»:=n},0#usize)
  (by change n.val-0<n.val+1;omega)
 change (do let (calls,pending) ← loop (body stop) ({start:=0#usize,«end»:=n},0#usize)
            match pending with
            | none=>ok (core.result.Result.Ok (),calls)
            | some reply=>ok reply)=_
 rw [eqn]

#print axioms progress
#print axioms decreases
#print axioms source
end NHM_ControlLoop
