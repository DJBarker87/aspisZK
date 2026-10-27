import XRk_GeometryStep
import XRk_LoopInvariant
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools
namespace XRk_GeometryProjection
open XRk_GeometryStep

theorem loop_start (start : Usize) (it : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec aspis_core.field.M31) (g : verifier.QueryGeometry)
    (run : verifier.QueryGeometry.for_range_loop0 it start lines flat=ok (.Ok g)) :
    g.start=start := by
  exact XRk_LoopInvariant.preserve
    (fun s : State => verifier.QueryGeometry.for_range_loop0.body start s.1 s.2.1 s.2.2)
    (post start) measure
    (fun s out run => by
      rcases s with ⟨it,lines,flat⟩
      cases out <;> exact step start it lines flat _ run)
    (it,lines,flat) (.Ok g) run

theorem start (queries : Array U32 22#usize) (startInput finish : Usize) (g : verifier.QueryGeometry)
    (run : verifier.QueryGeometry.for_range queries startInput finish=ok (.Ok g)) :
    g.start=startInput := by
  unfold verifier.QueryGeometry.for_range at run
  split at run
  · cases run
  · try simp only [lift,bind_tc_ok] at run
    split at run
    · cases run
    · obtain ⟨length,_,run⟩ := bind_success _ _ _ run
      obtain ⟨flatLength,_,run⟩ := bind_success _ _ _ run
      obtain ⟨slice,_,run⟩ := bind_success _ _ _ run
      obtain ⟨it,_,run⟩ := bind_success _ _ _ run
      exact loop_start startInput it _ _ g run
#print axioms loop_start
#print axioms start
end XRk_GeometryProjection
