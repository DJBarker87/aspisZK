import GeometryGroupingArrayModel
import StableArrayFromFnTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec AspisR1GeometryGrouping.Proof
private abbrev GroupCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31

theorem geometry_group_array_total (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val < end1.val-start.val) :
    geometryArrayWithFromFnModel inverse i = .ok (flatInverseArray inverse i) := by
  let value : Nat → U32 := fun j => inverse.val.getD (5*i.val+j) 0#u32
  have hstable : ∀ j : Usize, j.val < (5#usize : Usize).val →
      GroupCallback.call_mut (inverse,i) j = .ok (value j.val,(inverse,i)) := by
    intro j hj
    exact geometry_callback_total queries start end1 i j inverse zs hrun hi hj
  obtain ⟨out,hout,hvals⟩ := AspisR1SelectedMaskProbe.arrayFromFn_stable_total GroupCallback value (inverse,i) hstable
  have he : out=flatInverseArray inverse i := by
    apply Subtype.ext
    rw [hvals]
    rfl
  change AspisR1SelectedMaskProbe.core.array.from_fn 5#usize GroupCallback (inverse,i) = _
  rw [←he]
  exact hout

#print axioms geometry_group_array_total
end AspisR1CurrentWide.Proof
