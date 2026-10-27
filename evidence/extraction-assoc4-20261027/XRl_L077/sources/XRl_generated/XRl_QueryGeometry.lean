import XRl_GeometryLengths
import XRl_GeometryInput
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRl_QueryGeometry
/-- Cardinalities for the actual emitted entry point, deriving the input
slice span from its SAME successful array read. Includes native-library model
errors as modeled; this is not allocator/compiled-source P6. -/
theorem lengths (queries : Array U32 22#usize) (start finish : Usize) (g : verifier.QueryGeometry)
    (run : verifier.QueryGeometry.for_range queries start finish=ok (.Ok g)) :
    g.line_z.val.length=finish.val-start.val ∧ g.inverses.val.length=finish.val-start.val := by
  unfold verifier.QueryGeometry.for_range at run
  split at run
  · cases run
  · try simp only [lift,bind_tc_ok] at run
    split at run
    · cases run
    · obtain ⟨length,_,run⟩ := bind_success _ _ _ run
      obtain ⟨flatLength,_,run⟩ := bind_success _ _ _ run
      obtain ⟨slice,hslice,run⟩ := bind_success _ _ _ run
      obtain ⟨it,hit,run⟩ := bind_success _ _ _ run
      have span := XRl_GeometryInput.range queries start finish slice hslice
      have same := Result.ok.inj hit
      subst it
      apply XRl_GeometryLengths.loop (finish.val-start.val) start _ _ _ g ?_ run
      constructor
      · change 0+(slice.val.length-0)=finish.val-start.val
        simpa only [Nat.zero_add,Nat.sub_zero] using span.2.2
      · rfl

theorem queryGeometryLineInvariant : XRk_Association.QueryGeometryLineInvariant := by
  intro queries start finish g run
  have size := lengths queries start finish g run
  exact ⟨XRk_GeometryProjection.start queries start finish g run,size.2,size.1⟩
#print axioms lengths
#print axioms queryGeometryLineInvariant
end XRl_QueryGeometry
