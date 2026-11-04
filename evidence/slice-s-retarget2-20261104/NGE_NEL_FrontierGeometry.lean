import Lean
import NFY_Part032

set_option autoImplicit false
namespace NGE_NEL_FrontierGeometry

theorem bounds (level offset : Nat) (word : level < 20) (byte : offset < 32) :
    160+32*level+offset < 800 ∧ 48+32*level+offset < 688 ∧
    160+32*level+32 ≤ 800 ∧ 48+32*level+32 ≤ 688 ∧ level+1 ≤ 20 := by omega

theorem coordinate_unique (base i j k l : Nat) (ki : k < 32) (lj : l < 32)
    (same : base+32*i+k = base+32*j+l) : i = j ∧ k = l := by omega

theorem header_disjoint (level k : Nat) (header : k < 24) :
    k < 32 ∧ k < 160+32*level ∧ k < 48+32*level := by omega

#print axioms bounds
#print axioms coordinate_unique
#print axioms header_disjoint
end NGE_NEL_FrontierGeometry

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
