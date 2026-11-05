import NGW_ConstructorPoints
import NGW_ReverseInduction
import NGW_ProductLaw
set_option autoImplicit false
namespace NGW_PointsPacket
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_ConstructorArrays

def reference (z : Array Q 10#usize) : Result (Array (Array Q 10#usize) 3#usize) := do
 let successor ← NGW_ReverseInduction.reference 10 (NGW_Reverse.cursor 10#usize) z z
   FIn_WeightsExtract.field.QM31.ONE
 let old7 ← Array.index_usize z 7#usize
 let diff7 ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE old7
 let first ← Array.update z 7#usize diff7
 let old6 ← Array.index_usize first 6#usize
 let diff6 ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE old6
 let absorbed ← Array.update first 6#usize diff6
 ok (Array.make 3#usize [z,successor,absorbed])

theorem source (z : Array Q 10#usize) :
 FIn_WeightsExtract.state_only_prefix.state_only_statement_points z=reference z := by
 have size : Slice.len z.to_slice=10#usize := by
   apply UScalar.eq_of_val_eq
   exact z.property
 have reverse : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      {start:=0#usize,«end»:=10#usize}=ok (NGW_Reverse.cursor 10#usize) := by rfl
 unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points reference
 simp only [lift,bind_tc_ok,size,reverse]
 rw [NGW_ReverseInduction.source 10 z z FIn_WeightsExtract.field.QM31.ONE 10#usize (by decide)]

theorem cohort (z : Array Q 10#usize) (canonical : Holds Canon z) :
 ∃ out, reference z=ok out ∧
 FIn_WeightsExtract.state_only_prefix.state_only_statement_points z=ok out ∧
 FIn_WeightsExtract.state_only_prefix.r0.statement_points z=ok out ∧
 Holds (Holds Canon) out := by
 obtain ⟨out,run,canonicalOut⟩ := NGW_ConstructorPoints.source z canonical
 exact ⟨out,(source z).symm.trans run,run,run,canonicalOut⟩

#print axioms source
#print axioms cohort
end NGW_PointsPacket
