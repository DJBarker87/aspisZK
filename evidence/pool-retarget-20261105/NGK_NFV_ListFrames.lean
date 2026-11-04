import Lean
import NGK_NFV_Copy

set_option autoImplicit false
namespace NGK_NFV_ListFrames

theorem set_next {T : Type} (head tail : List T) (old value : T) :
    (head ++ old::tail).set head.length value = head ++ value::tail := by
  induction head with
  | nil => rfl
  | cons first rest ih => simpa [List.set] using congrArg (List.cons first) ih
#print axioms set_next

theorem copy_next {T : Type} (head src : List T) (zero : T) (remaining : Nat)
    (fits : src.length ≤ remaining) :
    (head ++ List.replicate remaining zero).setSlice! head.length src =
      head ++ src ++ List.replicate (remaining-src.length) zero := by
  simp [List.setSlice!,List.take_append,List.drop_append,Nat.min_eq_left fits,List.append_assoc]
#print axioms copy_next
theorem copy_at {T : Type} (head src : List T) (zero : T) (remaining start : Nat)
    (position : start = head.length) (fits : src.length ≤ remaining) :
    (head ++ List.replicate remaining zero).setSlice! start src =
      head ++ src ++ List.replicate (remaining-src.length) zero := by
  subst start
  exact copy_next head src zero remaining fits
#print axioms copy_at
end NGK_NFV_ListFrames

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
