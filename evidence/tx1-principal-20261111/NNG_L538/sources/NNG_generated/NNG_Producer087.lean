import NNG_Erase087
import NNG_PrepareInput087
import NNG_Events087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Producer087
open Aeneas Aeneas.Std NMP_Emitted NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

theorem source {H W : Type} (env : RSL.Env) (s : Parent H W) :
 erase (NNG_Tree087.tree (NNG_PrepareEmission087.calls env) s)=
 prepare (NNG_PrepareEmission087.calls env) s :=
 (NNG_Erase087.tree _ s).trans (NMP_PrepareSuffix.source _ s)

def producer (a : Args) (obs : RSL.Observer) (env : RSL.Env) :
 RSL.Obs (Except LIB_Instances.VL.VErr LIB_Instances.VL.Prepared × LIB_Instances.VL.E29) :=
 ⟨exit NNG_PreparedCall087.port (prepare (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)),
  (run (NNG_Tree087.tree (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env))).2.flatMap (NNG_Events087.events env)⟩

theorem tree (a : Args) (obs : RSL.Observer) (env : RSL.Env) :
 producer a obs env=observation NNG_PreparedCall087.port (NNG_Events087.events env)
  (NNG_Tree087.tree (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)) := by
 unfold producer observation
 dsimp only
 rw [run_result,source]
#print axioms source
#print axioms tree
end AspisR1.NNG_Producer087
