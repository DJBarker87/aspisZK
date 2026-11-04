import Lean
import NFY_Part032
import NFY_Part029

set_option autoImplicit false
namespace NGE_NEL_DigestGeometry

theorem window_bound (index offset : Nat) (word : index < 8) (byte : offset < 4) :
    4*index+offset < 32 ∧ 4*index+4 ≤ 32 ∧ index+1 ≤ 8 := by omega

theorem distinct_words (i j : Nat) (different : i < j) : 4*i+4 ≤ 4*j := by omega

/-- The physical byte cannot silently refer to another digest limb or offset. -/
theorem coordinate_unique (i j k l : Nat) (ki : k < 4) (lj : l < 4)
    (same : 4*i+k = 4*j+l) : i = j ∧ k = l := by omega

#print axioms window_bound
#print axioms distinct_words
#print axioms coordinate_unique
end NGE_NEL_DigestGeometry

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
