import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue050
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i)) : Result (core.result.Result host_commitment.Word aspis_core.r0.Error) := do
  let (r, _) := out
  ok r

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once (c := c) (i := i) =
      (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i >>= fun out => continueAfter (c := c) (i := i) out) := by
  rw [host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) (out : Payload (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i))
    (h : (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i) = .ok out) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once (c := c) (i := i) = continueAfter (c := c) (i := i) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize) (e : Error)
    (h : (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i) = .fail e) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once (c := c) (i := i) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (c : host_commitment.encode_commitment_words.closure_1) (i : Std.Usize)
    (h : (host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeResultWordError.call_mut
      c i) = .div) :
    host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeResultWordError.call_once (c := c) (i := i) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue050
