import Aeneas
import NEG_RowIsolated.Types
set_option autoImplicit false
namespace NEG_RowIsolated
open Aeneas Aeneas.Std Result
/-- Concrete standard-library delegation. The generated external template used
`IterMut T → Array T N`, which is incompatible with the emitted call's transformer
continuation. This explicit repaired interface is a MODEL, pending native/library
association; no D188 credit is inferred merely from compilation. -/
def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Usize} (a : Array T N) :
    Result (core.slice.iter.IterMut T ×
      ((core.slice.iter.IterMut T → core.slice.iter.IterMut T) → Array T N)) := do
  let (s, arrayBack) ← lift (Array.to_slice_mut a)
  let (it, sliceBack) ← core.slice.Slice.iter_mut s
  ok (it, fun transform => arrayBack (sliceBack (transform it)))

#print axioms MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
end NEG_RowIsolated
