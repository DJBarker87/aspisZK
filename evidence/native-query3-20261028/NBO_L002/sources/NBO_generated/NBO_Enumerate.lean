import NBO_FinishCaller
import S8Kani2FinishCertificate
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBO_Enumerate
open S8Kani2MutableExtraction.batched_weights S8Kani2MutableValue
/-- Full actual emitted Enumerate/back-continuation traversal from any
valid cursor, including exhaustion. Values are derived from the SAME raw
producer, rather than supplied as a separate successful child execution.
The destination's own bound supplies usize capacity for the ordinal. -/
theorem from_cursor (self : F.BW) (initial : FinishIter)
 (cursor : initial.iter.i ≤ initial.iter.slice.len.val)
 (ordinal : initial.count.val=initial.iter.i)
 (lengths : initial.iter.slice.val.length≤self.raw.length) :
 ∃ output : FinishIter,
   BatchedWeights.finish_loop initial (fun e=>e) self=ok output ∧
   output.iter.slice=prefixWrite (valueAt self) initial.iter.i
     initial.iter.slice.len.val initial.iter.slice := by
 apply finish_loop_output_invariant_of_values self initial (valueAt self) cursor ordinal
 · intro i hi
   apply valueAt_success
   change i.val<initial.iter.slice.val.length at hi
   exact lt_of_lt_of_le hi lengths
 · exact initial.iter.slice.property
#print axioms from_cursor
end NBO_Enumerate
