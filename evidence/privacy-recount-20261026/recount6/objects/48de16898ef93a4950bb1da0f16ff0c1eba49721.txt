import R1Z.PV_RW_IteratorStateSource
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18InlineContext
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev Iter := core.slice.iter.Iter U32
variable [ExternalTypes] [ExternalFuns]

-- Literal inline for-loop context, separated from the sibling-owned source
-- identity. This declaration alone is not an extraction of op223.
def body (lambda : Q) (iterator : Iter) (out power : Q) :
    Result (ControlFlow (Iter × Q × Q) Q) := do
  let (head,next) ← core.slice.iter.IteratorSliceIter.next iterator
  match head with
  | none => ok (done out)
  | some value =>
    let scaled ← aspis_core.field.QM31.mul_m31 power value
    let out1 ← aspis_core.field.QM31.add out scaled
    let power1 ← aspis_core.field.QM31.mul power lambda
    ok (cont (next,out1,power1))

def run (lambda : Q) (iterator : Iter) (out power : Q) : Result Q :=
  loop (fun (iterator,out,power) => body lambda iterator out power) (iterator,out,power)

def bounded (lambda : Q) : Nat → Iter → Q → Q → Result Q
  | 0, _, _, _ => .div
  | fuel+1, iterator, out, power => do
    let flow ← body lambda iterator out power
    match flow with
    | .done final => ok final
    | .cont (next,out1,power1) => bounded lambda fuel next out1 power1

theorem unfold_run (lambda : Q) (iterator : Iter) (out power : Q) :
    run lambda iterator out power = (do
      let flow ← body lambda iterator out power
      match flow with
      | .done final => ok final
      | .cont (next,out1,power1) => run lambda next out1 power1) := by
  unfold run
  rw [ProverRw19LoopBind.loop_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro flow _
  cases flow with
  | done final => rfl
  | cont pair => rcases pair with ⟨next,out1,power1⟩; rfl

#print axioms unfold_run
end R1Z.ProverRw18InlineContext
