import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue049
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut`.
Recursive calls remain the original extracted calls. -/
def continueAfter (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args)) : Result ((core.result.Result host_commitment.Word aspis_core.r0.Error) ×
    host_commitment.encode_commitment_words.closure_1) := do
  let r := out
  ok (r, state)

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut (state := state) (args := args) =
      (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args >>= fun out => continueAfter (state := state) (args := args) out) := by
  rw [host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args))
    (h : (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args) = .ok out) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut (state := state) (args := args) = continueAfter (state := state) (args := args) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize) (e : Error)
    (h : (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args) = .fail e) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut (state := state) (args := args) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (state : host_commitment.encode_commitment_words.closure_1) (args : Std.Usize)
    (h : (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError.call
      state args) = .div) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut (state := state) (args := args) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue049
