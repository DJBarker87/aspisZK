import FIo_NativeFuns
import NDD_Reference.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_GuardModel
abbrev Q := FIo_Native.aspis_core.field.QM31
abbrev Row := Array Q 4#usize

def row (w : FIo_Native.weights.Weights) (k d : Usize) : Result Row := do
  let a ← Array.index_usize w.factors k
  Array.index_usize a d

/-- Comparison results and SAME row projections are explicit cut premises.
The remaining native/model equality-carrier association is not hidden here. -/
theorem cut (w : FIo_Native.weights.Weights) (folds : Usize)
    (a b c d : Row) (s2 first second : Bool)
    (hv : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
      w.variant FIo_Native.transport.Variant.S2 = ok s2)
    (h0 : row w 0#usize 2#usize = ok a) (h2 : row w 2#usize 2#usize = ok b)
    (h3 : row w 0#usize 3#usize = ok c) (h4 : row w 2#usize 3#usize = ok d)
    (ha : core.array.equality.PartialEqArray.eq
      FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a b = ok first)
    (hb : core.array.equality.PartialEqArray.eq
      FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c d = ok second) :
    FIo_Native.weights.shared_two_point_guard w folds =
      NDD_Reference.guard_ref s2 folds first second := by
  simp [row,Array.index_usize] at h0 h2 h3 h4
  simp [FIo_Native.weights.shared_two_point_guard,hv,
    Array.index_usize,h0,h2,h3,h4,ha,hb,NDD_Reference.guard_ref]
#print axioms cut
end NDD_GuardModel
