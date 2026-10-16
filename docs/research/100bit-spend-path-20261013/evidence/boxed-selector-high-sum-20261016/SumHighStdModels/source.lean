import SelectorValueLaneGeneratedSlice

/-! Explicit standard-library model of derived Range.clone. The pinned Rust
Range has two fields and derives Clone. This model delegates each field to
its supplied clone implementation; no external axiom or success stub is used.
Compiler/derive and library-model correspondence remain a stated TCB boundary. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1SumHighCandidate

def core.ops.range.Range.Insts.CoreCloneClone.clone {T : Type}
    (cloneInst : Aeneas.Std.core.clone.Clone T)
    (r : Aeneas.Std.core.ops.range.Range T) : Result (Aeneas.Std.core.ops.range.Range T) := do
  let start ← cloneInst.clone r.start
  let finish ← cloneInst.clone r.end
  .ok { start := start, «end» := finish }

theorem clone_usize (r : Aeneas.Std.core.ops.range.Range Usize) :
    core.ops.range.Range.Insts.CoreCloneClone.clone Aeneas.Std.core.clone.CloneUsize r = .ok r := by
  rfl

#print axioms clone_usize
end AspisR1SumHighCandidate
