import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue011
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.opening_lane_values`.
Recursive calls remain the original extracted calls. -/
def continueAfter (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) (out : Payload (aspis_core.r0.domain.FibreIndex.get u)) : Result (Array aspis_core.field.wide_exact.WideExact 4#usize) := do
  let i := out
  let at1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i)
  let we ← host_commitment.Word.value word at1
  let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize)
  let we1 ← host_commitment.Word.value word i1
  let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize)
  let we2 ← host_commitment.Word.value word i2
  let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize)
  let we3 ← host_commitment.Word.value word i3
  ok (Array.make 4#usize [ we, we1, we2, we3 ])

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) :
    host_commitment.opening_lane_values (word := word) (u := u) =
      (aspis_core.r0.domain.FibreIndex.get u >>= fun out => continueAfter (word := word) (u := u) out) := by
  rw [host_commitment.opening_lane_values]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) (out : Payload (aspis_core.r0.domain.FibreIndex.get u))
    (h : (aspis_core.r0.domain.FibreIndex.get u) = .ok out) :
    host_commitment.opening_lane_values (word := word) (u := u) = continueAfter (word := word) (u := u) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) (e : Error)
    (h : (aspis_core.r0.domain.FibreIndex.get u) = .fail e) :
    host_commitment.opening_lane_values (word := word) (u := u) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex)
    (h : (aspis_core.r0.domain.FibreIndex.get u) = .div) :
    host_commitment.opening_lane_values (word := word) (u := u) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue011
