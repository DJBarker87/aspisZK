import GeometryGroupingArrayTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec AspisR1GeometryGrouping.Proof
private abbrev Capture := AspisR1GeometryGrouping.geometry_groups.closure
private abbrev InnerCapture := AspisR1GeometryGrouping.geometry_groups.closure.closure
private abbrev GroupCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31

def groupingOuterWithFromFn
    (fromFn : (n : Usize) → core.ops.function.FnMut InnerCapture Usize U32 →
      InnerCapture → Result (Array U32 n))
    (c : Capture) (tupled_args : Usize) : Result ((Array U32 5#usize) × Capture) := do
  let a ← fromFn 5#usize GroupCallback (c,tupled_args)
  ok (a,c)

theorem geometry_group_outer_total (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val < end1.val-start.val) :
    groupingOuterWithFromFn AspisR1SelectedMaskProbe.core.array.from_fn inverse i =
      .ok (flatInverseArray inverse i,inverse) := by
  have hgroup := geometry_group_array_total queries start end1 i inverse zs hrun hi
  change AspisR1SelectedMaskProbe.core.array.from_fn 5#usize GroupCallback (inverse,i) = _ at hgroup
  unfold groupingOuterWithFromFn
  rw [hgroup]
  rfl

#print axioms geometry_group_outer_total
end AspisR1CurrentWide.Proof
