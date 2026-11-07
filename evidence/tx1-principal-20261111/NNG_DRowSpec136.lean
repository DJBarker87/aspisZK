import NNG_DSourceRounds
import NNG_EnvOccurrences136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DRowSpec136
open NNG_Emitted NNG_DProjection136 NNG_DOccurrenceLaws136

/-- Full source fold into the literal rev3 row. Every call law is local to
one actual input/Env/trace. This is conditional support: a candidate must
install the packet from LIB's concrete VL and CLOSED deterministic models. -/
theorem fold (VL : RSL.VLib) {H W : Type}
    (project : RSL.TX1_136.Args VL → Representation VL H)
    (calls : RSL.TX1_136.Args VL → RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.TX1_136.Args VL → RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (closedOccurrences : ∀ a obs env, RSL.TX1_136.Domain VL a →
      Laws VL a (project a) (calls a env) (input a obs env) (events a) env
        (NNG_FinishTree.tree (calls a env) (input a obs env))) :
    RSL.TX1_136.RowSpec_136 VL (NNG_DEnvObserved136.producer VL project calls input events) := by
  intro a obs env domain
  rw [NNG_DEnvObserved136.producer_tree,NNG_TreeEmission.tree_suffixes]
  rw [←NNG_Canonical136.body_ref]
  apply NNG_DSourceRounds.source
  have laws := closedOccurrences a obs env domain
  rw [NNG_TreeEmission.tree_suffixes] at laws
  exact laws
#print axioms fold
end AspisR1.NNG_DRowSpec136
