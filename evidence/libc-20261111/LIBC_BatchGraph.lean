import LIBC_BatchMerkle
set_option autoImplicit false
noncomputable section
namespace LIBC_BatchGraph
open Aeneas Aeneas.Std Result RSL
open LIBC_BatchMerkle
theorem graph (a : Args) (env : Env) (o : Obs Output) :
 child.law a env o ↔ o=LIB_Carriers.resultObs port (render (history a env)) (model a env) := Iff.rfl
theorem returned (a : Args) (env : Env) (r : Output) (ev : List Event) :
 child.law a env ⟨.ret r,ev⟩ ↔ ∃ native,
 model a env=.ok native ∧ r=port native ∧ ev=render (history a env) := by
 cases h : model a env <;> simp [child,LIB_Carriers.resultGraph,LIB_Carriers.resultObs,h]
theorem functional (a : Args) : Child.Functional child := by
 intro x env o₁ o₂ h₁ h₂
 exact h₁.trans h₂.symm
/-- The checksum/folded-root input is the exact original B32, not a
separately selected root or digest. -/
theorem folded_same (a : Args) : LIB_Carriers.b32 (folded a)=a.2.2.1 := LIB_Env.key_roundtrip _
#print axioms graph
#print axioms returned
#print axioms functional
#print axioms folded_same
end LIBC_BatchGraph
