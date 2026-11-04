import Lean
import NFY_Part031

set_option autoImplicit false
namespace NGE_NEJ_WindowStep
open KMX_CopyMeaning

/-- Value operation of exactly one KMX indexed iteration on a caller window. -/
def step {α : Type} (dst src : Nat → α) (start offset : Nat) : Nat → α :=
  write dst (start+offset) (src offset)

/-- Native step's local source index is the same global destination cell. -/
theorem association {α : Type} (dst src : Nat → α) (start offset : Nat) :
    step dst src start offset =
      write dst (start+offset) ((fun k => src (k-start)) (start+offset)) := by
  simp only [step, Nat.add_sub_cancel_left]

/-- Induction covers an arbitrary suffix from the caller-established invariant,
not only an initially zero buffer or a concrete iteration count. -/
theorem iteration {α : Type} (dst src : Nat → α) (start offset count k : Nat) :
    loop (fun j => src (j-start)) dst (start+offset) count k =
      if start+offset ≤ k ∧ k < start+offset+count then src (k-start) else dst k :=
  loop_spec _ _ _ _ _

/-- The remaining copy suffix cannot overwrite an already-written earlier cell. -/
theorem earlier_frame {α : Type} (dst src : Nat → α) (start offset count k : Nat)
    (before : k < start+offset) :
    loop (fun j => src (j-start)) dst (start+offset) count k = dst k :=
  copy_frame _ _ _ _ _ (Or.inl before)

/-- A caller's fixed-array widths give the exact loop termination invariant. -/
theorem bounds (start width offset : Nat) (within : offset < width)
    (fits : start+width ≤ 216) :
    start+offset < 216 ∧ offset+1 ≤ width ∧ width-(offset+1) < width-offset := by
  omega

#print axioms association
#print axioms iteration
#print axioms earlier_frame
#print axioms bounds
end NGE_NEJ_WindowStep

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
