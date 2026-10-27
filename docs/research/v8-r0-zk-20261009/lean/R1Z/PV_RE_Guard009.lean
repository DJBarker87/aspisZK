import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard009
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue (h : Array aspis_core.field.wide_exact.WideExact 4#usize) (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool) : Result aspis_core.field.wide_exact.WideExact := do
    let we ← Array.index_usize h 0#usize
    let we1 ← Array.index_usize h 3#usize
    let we2 ← Array.index_usize h 2#usize
    let we3 ← Array.index_usize h 1#usize
    let we4 ← aspis_core.field.wide_exact.WideExact.mul alpha we3
    let we5 ← aspis_core.field.wide_exact.WideExact.add we2 we4
    let we6 ← aspis_core.field.wide_exact.WideExact.mul alpha we5
    let we7 ← aspis_core.field.wide_exact.WideExact.add we1 we6
    let we8 ← aspis_core.field.wide_exact.WideExact.mul alpha we7
    let we9 ← aspis_core.field.wide_exact.WideExact.add we we8
    aspis_core.field.wide_exact.WideExact.mul_m31 we9 weights.QUARTER

def onFalse (h : Array aspis_core.field.wide_exact.WideExact 4#usize) (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool) : Result aspis_core.field.wide_exact.WideExact := do
    let we ← Array.index_usize h 0#usize
    let we1 ← Array.index_usize h 1#usize
    let we2 ← Array.index_usize h 2#usize
    let we3 ← Array.index_usize h 3#usize
    let we4 ← aspis_core.field.wide_exact.WideExact.mul alpha we3
    let we5 ← aspis_core.field.wide_exact.WideExact.add we2 we4
    let we6 ← aspis_core.field.wide_exact.WideExact.mul alpha we5
    let we7 ← aspis_core.field.wide_exact.WideExact.add we1 we6
    let we8 ← aspis_core.field.wide_exact.WideExact.mul alpha we7
    aspis_core.field.wide_exact.WideExact.add we we8

/-- Exact first guard of `prover.fold_cell`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (h : Array aspis_core.field.wide_exact.WideExact 4#usize) (alpha : aspis_core.field.wide_exact.WideExact) (dual : Bool) :
  prover.fold_cell (h := h) (alpha := alpha) (dual := dual) =
    (if dual then onTrue (h := h) (alpha := alpha) (dual := dual) else onFalse (h := h) (alpha := alpha) (dual := dual)) := by
  rw [prover.fold_cell]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard009
