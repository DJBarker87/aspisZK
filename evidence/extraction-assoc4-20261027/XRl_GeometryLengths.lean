import XRl_GeometryStep
import XRl_LoopInvariant
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release
namespace XRl_GeometryLengths
open XRl_GeometryStep

theorem loop (n : Nat) (start : Usize) (it : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec aspis_core.field.M31) (g : verifier.QueryGeometry)
    (shape : Inv n it lines flat)
    (run : verifier.QueryGeometry.for_range_loop0 it start lines flat=ok (.Ok g)) :
    g.line_z.val.length=n ∧ g.inverses.val.length=n := by
  exact XRl_LoopInvariant.preserve
    (fun s : State => verifier.QueryGeometry.for_range_loop0.body start s.1 s.2.1 s.2.2)
    (fun s => Inv n s.1 s.2.1 s.2.2) (post n) measure
    (fun s out inv run => by
      rcases s with ⟨it,lines,flat⟩
      cases out <;> exact step n start it lines flat _ inv run)
    (it,lines,flat) (.Ok g) shape run
#print axioms loop
end XRl_GeometryLengths
