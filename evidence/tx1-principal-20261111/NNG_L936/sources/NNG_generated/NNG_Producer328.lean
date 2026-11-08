import NNG_Tree328
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Producer328
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136

def producer (a : NNG_Input094.Args) (env : RSL.Env) : RSL.Obs (Except RSL.ProgramError RSL.Bytes) :=
 ⟨exit NNG_Carriers328.port (NNG_Native328.body (NNG_Native328.input a) env),
  (run (NNG_Tree328.tree (NNG_Native328.input a) env)).2.flatMap (NNG_Tree328.events env)⟩

theorem tree (a : NNG_Input094.Args) (env : RSL.Env) :
 producer a env=observation NNG_Carriers328.port (NNG_Tree328.events env)
  (NNG_Tree328.tree (NNG_Native328.input a) env) := by
 unfold producer observation
 dsimp only
 rw [run_result,NNG_Tree328.source]
 rfl
#print axioms tree
end AspisR1.NNG_Producer328
