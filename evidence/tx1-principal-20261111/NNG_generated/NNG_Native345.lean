import NNG_Tree345
import NNG_Events345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Native345
open Aeneas Aeneas.Std NMT_345 NMT_CallTree NNG_Observed136

/-- Fixed fresh emitted-parent observation on native arguments. This is a
source adapter, not the canonical RowSpec345 candidate: native/logical parent
and reached-frame association is still required. -/
def producer {W : Type} (a : Parent W) (env : RSL.Env) : RSL.Obs (Except RSL.ProgramError RSL.Bytes) :=
 ⟨exit NNG_ChildSource345.port (emitted (NNG_Calls345.calls env) a),
 (run (NNG_Tree345.tree (NNG_Calls345.calls env) a)).2.flatMap (NNG_Events345.events env)⟩

theorem source {W : Type} (a : Parent W) (env : RSL.Env) :
 producer a env=observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_Tree345.tree (NNG_Calls345.calls env) a) := by
 unfold producer observation
 dsimp only
 rw [run_result,NNG_Tree345.source]
#print axioms source
end AspisR1.NNG_Native345
