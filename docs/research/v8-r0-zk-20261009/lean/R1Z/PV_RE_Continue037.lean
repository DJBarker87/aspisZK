import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue037
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.semantic_error`.
Recursive calls remain the original extracted calls. -/
def continueAfter (e : r1_wire.Error) (out : Payload (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole)) : Result verifier.Error := do
  let b := out
  if b
  then ok verifier.Error.Rejected
  else ok verifier.Error.Semantic

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (e : r1_wire.Error) :
    prover.semantic_error (e := e) =
      (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole >>= fun out => continueAfter (e := e) out) := by
  rw [prover.semantic_error]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (e : r1_wire.Error) (out : Payload (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole))
    (h : (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole) = .ok out) :
    prover.semantic_error (e := e) = continueAfter (e := e) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (e : r1_wire.Error) (e : Error)
    (h : (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole) = .fail e) :
    prover.semantic_error (e := e) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (e : r1_wire.Error)
    (h : (r1_wire.Error.Insts.CoreCmpPartialEqError.eq e r1_wire.Error.ActivePole) = .div) :
    prover.semantic_error (e := e) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue037
