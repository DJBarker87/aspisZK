import R1Z.ProverRwP6CompressControl
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressList
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]
-- Preserve the power update, including its failure or divergence, even on
-- the final element. This is the owned reference's exact operation order.
def stateFold : List M → Q → Q × Q → Result (Q × Q)
  | [], _, state => ok state
  | m::ms, lambda, (out,power) => do
    let q ← aspis_core.field.QM31.mul_m31 power m
    let out1 ← aspis_core.field.QM31.add out q
    let power1 ← aspis_core.field.QM31.mul power lambda
    stateFold ms lambda (out1,power1)

def fold (xs : List M) (lambda out power : Q) : Result Q := do
  let pair ← stateFold xs lambda (out,power)
  ok pair.1

theorem nil (lambda out power : Q) : fold [] lambda out power = ok out := rfl

theorem cons (m : M) (ms : List M) (lambda out power : Q) :
    fold (m::ms) lambda out power = (do
      let q ← aspis_core.field.QM31.mul_m31 power m
      let out1 ← aspis_core.field.QM31.add out q
      let power1 ← aspis_core.field.QM31.mul power lambda
      fold ms lambda out1 power1) := by
  simp only [fold,stateFold,bind_assoc_eq]

-- An exact composition law, including every Result branch and updated power.
theorem append (xs ys : List M) (lambda : Q) (state : Q × Q) :
    stateFold (xs++ys) lambda state =
      (stateFold xs lambda state >>= stateFold ys lambda) := by
  induction xs generalizing state with
  | nil => simp only [List.nil_append,stateFold,bind_tc_ok]
  | cons m ms ih =>
    rcases state with ⟨out,power⟩
    simp only [List.cons_append,stateFold,bind_assoc_eq]
    repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    exact ih _
#print axioms nil
#print axioms cons
#print axioms append
end R1Z.PV_CompressList
