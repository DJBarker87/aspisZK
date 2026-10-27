import R1Z.ProverRwSuccessOptions
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessField
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
-- Structural source operations; no raw-limb canonicality restriction.
def clone (x : W) : Result W := .ok x
def eq (x y : W) : Result Bool := do
  let equal ← ProverRwDictionaryDerived.qEq x.c0 y.c0
  if equal then ProverRwDictionaryDerived.qEq x.c1 y.c1 else .ok false
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessOptions.selected ops with
    op40 := clone, op41 := eq, op43 := fun x => .ok x.c0,
    op44 := fun x => .ok x.c1}
attribute [local instance] Classical.propDecidable

theorem clone_total (ops : ExternalFuns) (x : W) :
    (selected ops).op40 x = .ok x := rfl

theorem eq_total (ops : ExternalFuns) (x y : W) :
    (selected ops).op41 x y = .ok (decide (x=y)) := by
  change eq x y = _
  unfold eq
  rw [ProverRwDictionaryDerived.q_status]
  cases x with
  | mk a b =>
    cases y with
    | mk c d =>
      by_cases h : a=c <;> by_cases k : b=d <;>
        simp [h,k,ProverRwDictionaryDerived.q_status]

theorem c0_total (ops : ExternalFuns) (x : W) :
    (selected ops).op43 x = .ok x.c0 := rfl

theorem c1_total (ops : ExternalFuns) (x : W) :
    (selected ops).op44 x = .ok x.c1 := rfl
#print axioms clone_total
#print axioms eq_total
#print axioms c0_total
#print axioms c1_total
end R1Z.ProverRwSuccessField
