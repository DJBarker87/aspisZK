import GeometryFlatFoldSource
import QueryScanConcreteWordsDecoder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open AspisR1GeometryInputs.Proof Aeneas.Std.alloc.vec AspisR1GeometryGrouping.Proof
private abbrev GroupCallback := AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31

def geometryArrayWithFromFnModel (flat : Vec U32) (i : Usize) : Result (Array U32 5#usize) :=
  AspisR1SelectedMaskProbe.core.array.from_fn 5#usize GroupCallback (flat,i)

theorem geometry_group_array_success (queries : Array U32 22#usize)
    (start end1 i : Usize) (inverse zs : Vec U32)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (hi : i.val < end1.val-start.val) (out : Array U32 5#usize)
    (hgroup : geometryArrayWithFromFnModel inverse i = .ok out) :
    out = flatInverseArray inverse i := by
  let value : Nat → U32 := fun j => inverse.val.getD (5*i.val+j) 0#u32
  have h5 : (5#usize : Usize).val=5 := rfl
  have h0 : (0#usize : Usize).val=0 := rfl
  have hstable : ∀ j : Usize, j.val < (5#usize : Usize).val →
      GroupCallback.call_mut (inverse,i) j = .ok (value j.val,(inverse,i)) := by
    intro j hj
    exact geometry_callback_total queries start end1 i j inverse zs hrun hi hj
  unfold geometryArrayWithFromFnModel AspisR1SelectedMaskProbe.core.array.from_fn at hgroup
  split at hgroup
  · rename_i values fout hloop
    have hout : (⟨values, by
        exact AspisR1SelectedMaskProbe.arrayFromFnLoop_length_of_success
          (5#usize) GroupCallback ((5#usize : Usize).val+1) 0#usize (inverse,i) []
          values fout (by rw [h0,h5]; omega) (by simp) (by omega) hloop⟩ :
        Array U32 5#usize) = out := Result.ok.inj hgroup
    have hvalues := AspisR1SelectedMaskProbe.arrayFromFnLoop_values_of_stable
      GroupCallback value ((5#usize : Usize).val+1) 0#usize (inverse,i) [] values fout
      (by rw [h0,h5]; omega) (by rw [h0,h5]; omega) (by simp [h0]) hstable hloop
    apply Subtype.ext
    have hv : values = (List.range 5).map value := by simpa only [h5] using hvalues.1
    have ho := congrArg (fun a : Array U32 5#usize => a.val) hout
    change values=out.val at ho
    rw [←ho,hv]
    rfl
  · simp at hgroup
  · have hdiv : div? (Result.div : Result (Array U32 5#usize)) = true := rfl
    rw [hgroup] at hdiv
    simp [div?] at hdiv

#print axioms geometry_group_array_success
end AspisR1CurrentWide.Proof
