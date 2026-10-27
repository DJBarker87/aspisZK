import XSe_ValidatorLoop
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ValidatorFold
/-- The actual standard chunks and enumeration are retained verbatim. -/
def run (row : U8) (payload : Slice U8) :
 Result (core.result.Result Unit XSe_ValidatorStage.OldError) := do
 let ce ← core.slice.Slice.chunks_exact payload 32#usize
 let iter ← core.iter.traits.iterator.Iterator.enumerate.trait_default
  (core.iter.traits.iterator.IteratorChunksExact U8) ce
 XRo_Join_Carriers.mapR XSe_EnumeratedDriver.finish
  (XSe_ListDriver.fold (XSe_EnumeratedDriver.step XSe_ValidatorIter.next
    (XSe_ValidatorStage.kit row)) iter.iter.chunks (.Ok iter.count))
/-- Whole old validator/fold equality; arbitrary row,payload and errors. -/
theorem source (row : U8) (payload : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload=run row payload := by
 unfold AspisR1PrefixAggregateParser.r1_wire.validate_record_fields run
 congr 1
 funext ce
 congr 1
 funext iter
 rw [XSe_ValidatorLoop.source]
 have same : XSe_ValidatorStage.old row=XSe_ValidatorStage.kit row :=
  funext (fun i => funext (XSe_ValidatorStage.source row i))
 unfold XSe_ValidatorIter.stage
 rw [same]
#print axioms source
end XSe_ValidatorFold
