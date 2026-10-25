import Port3_BatchStage

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Rejection
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

/-- Exact pending-return match at the end of the emitted batch_tree.
Its source occurrence is pinned by Port4B_source_audit.py. -/
def emittedReturn (idx : Indices) (val : Values)
    (pending : Option (core.result.Result Unit verifier.Error)) :
    Result (core.result.Result Unit verifier.Error × Indices × Values) :=
  match pending with
  | none => fail .panic
  | some r => ok (r,idx,val)

/-- Exact nonzero-padding exit of the emitted loop. This is a local branch,
not a claim that arbitrary abstract children describe a native execution. -/
def emittedPadding (idx : Indices) (val : Values) :
    Result (Indices × Values × Option (core.result.Result Unit verifier.Error)) :=
  ok (idx,val,none)

/-- Correct pending return for Rust's nonzero-padding Parse rejection. -/
def rustPadding (idx : Indices) (val : Values) :
    Result (Indices × Values × Option (core.result.Result Unit verifier.Error)) :=
  ok (idx,val,some (.Err verifier.Error.Parse))

/-- The branch carriers already differ before interpreting any oracle. -/
theorem padding_branch_differs (idx : Indices) (val : Values) :
    emittedPadding idx val ≠ rustPadding idx val := by
  simp [emittedPadding,rustPadding]

/-- Decoding that branch produces a panic; the corrected branch returns
Parse. Equal rejection Booleans cannot establish full Result equality. -/
theorem padding_result_differs (idx : Indices) (val : Values) :
    (do let (i,v,p) ← emittedPadding idx val; emittedReturn i v p) = fail .panic ∧
    (do let (i,v,p) ← rustPadding idx val; emittedReturn i v p) =
      ok (.Err verifier.Error.Parse,idx,val) ∧
    (do let (i,v,p) ← emittedPadding idx val; emittedReturn i v p) ≠
      (do let (i,v,p) ← rustPadding idx val; emittedReturn i v p) := by
  simp [emittedPadding,rustPadding,emittedReturn]

/-- Success is unaffected by this local decoder distinction. This does not
prove the native children, physical arguments or ordered-effects port. -/
theorem successful_return (idx : Indices) (val : Values) :
    emittedReturn idx val (some (.Ok ())) = ok (.Ok (),idx,val) := rfl

#print axioms padding_branch_differs
#print axioms padding_result_differs
#print axioms successful_return
end AspisR1.Port4B_Rejection
end
