import NNG_Erasure137
import NNG_Output137
import NNG_Events137
import NNG_Observed136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Producer137
open Aeneas Aeneas.Std NNG_Context137 NNG_Observed136 NMT_CallTree

def producer (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env) :
    RSL.Obs (Except LIB_VLib.library.WErr (RSL.Verified LIB_VLib.library)) :=
  ⟨exit (NNG_Output137.decode a env) (emitted (calls env) (input a obs env)),
   (run (NNG_Tree137.tree (calls env) (input a obs env))).2.flatMap (NNG_Events137.events env)⟩

theorem tree (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env) :
    producer a obs env = observation (NNG_Output137.decode a env) (NNG_Events137.events env)
      (NNG_Tree137.tree (calls env) (input a obs env)) := by
  unfold producer observation
  rw [run_result,NNG_Erasure137.source]
#print axioms tree
end AspisR1.NNG_Producer137
