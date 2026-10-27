import XRk_GeometryProjection
import XRl_MapCollector
import XRl_RangeMeasure
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_GeometryCollect
/-- Exact mapped dictionary used at the emitted geometry collector call. -/
abbrev callback := verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
abbrev iterator := XRl_MapCollector.iterator XRl_RangeMeasure.iterator callback
abbrev State := core.iter.adapters.map.Map (core.ops.range.Range Usize) (alloc.vec.Vec aspis_core.field.M31)

theorem list_length (s : State) (acc out : List (Array aspis_core.field.M31 5#usize))
    (run : alloc.vec.FromIteratorVec.iterToList iterator s acc=ok out) :
    out.length=acc.length+(s.iter.end.val-s.iter.start.val) := by
  have h := XRl_MapCollector.length XRl_RangeMeasure.iterator callback
    XRl_RangeMeasure.remaining XRl_RangeMeasure.terminal
    (fun s item next run => XRl_RangeMeasure.advance s next item run) s acc out run
  change out.length=acc.length+(s.iter.end.val-s.iter.start.val) at h
  omega

/-- Successful native-library collector modeling yields one inverse record
per base range iteration. The generated callback and all its errors are kept. -/
theorem length (s : State) (out : alloc.vec.Vec (Array aspis_core.field.M31 5#usize))
    (run : core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
      XRl_RangeMeasure.iterator callback
      (core.iter.traits.collect.FromIteratorVec (Array aspis_core.field.M31 5#usize)) s=ok out) :
    out.val.length=s.iter.end.val-s.iter.start.val := by
  unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
    core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.collect.FromIteratorVec alloc.vec.FromIteratorVec.from_iter at run
  simp only [core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter,bind_tc_ok] at run
  obtain ⟨xs,hxs,run⟩ := XRk_ResultTools.bind_success _ _ _ run
  change alloc.vec.FromIteratorVec.iterToList iterator s []=ok xs at hxs
  have size := list_length s [] xs hxs
  split at run
  · have same := Result.ok.inj run
    have val := congrArg (fun x : alloc.vec.Vec (Array aspis_core.field.M31 5#usize) => x.val.length) same
    simpa only [List.length_nil,Nat.zero_add] using val.symm.trans size
  · cases run
#print axioms list_length
#print axioms length
end XRl_GeometryCollect
