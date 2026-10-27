import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue047
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.Commitment.fill_opening`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) (pvBoundValue : Payload (host_commitment.fill_opening_values self u out.values 0#usize)) : Result aspis_core.r0.wire.FibreOpening := do
  let a := pvBoundValue
  let path ← host_commitment.opening_path self.time
  let a1 := Array.repeat 32#usize 0#u8
  let a2 := Array.repeat 7#usize a1
  let a3 := Array.repeat 6#usize a2
  let a4 ← Array.update out.paths path a3
  ok { values := a, paths := a4 }

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) :
    host_commitment.Commitment.fill_opening (self := self) (u := u) (out := out) =
      (host_commitment.fill_opening_values self u out.values 0#usize >>= fun pvBoundValue => continueAfter (self := self) (u := u) (out := out) pvBoundValue) := by
  rw [host_commitment.Commitment.fill_opening]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) (pvBoundValue : Payload (host_commitment.fill_opening_values self u out.values 0#usize))
    (h : (host_commitment.fill_opening_values self u out.values 0#usize) = .ok pvBoundValue) :
    host_commitment.Commitment.fill_opening (self := self) (u := u) (out := out) = continueAfter (self := self) (u := u) (out := out) pvBoundValue := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening) (e : Error)
    (h : (host_commitment.fill_opening_values self u out.values 0#usize) = .fail e) :
    host_commitment.Commitment.fill_opening (self := self) (u := u) (out := out) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex) (out : aspis_core.r0.wire.FibreOpening)
    (h : (host_commitment.fill_opening_values self u out.values 0#usize) = .div) :
    host_commitment.Commitment.fill_opening (self := self) (u := u) (out := out) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue047
