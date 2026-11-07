import NNG_InterpretProjection
import NNG_ProjectionLaws136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_EnvObserved136
open Aeneas Aeneas.Std Result NNG_Emitted NMT_CallTree NNG_Interpret136

/-- Runtime/allocator replies are interpreted at the SAME quantified Env.
In particular calls env may read env.reservation; fixing Calls outside the
Env quantifier would freeze this reply and cannot represent revision 3. -/
def producer {H W : Type} (VL : RSL.VLib) (p : NNG_Projection136.Representation VL H)
    (calls : RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    RSL.Obs (Except VL.WErr (RSL.Verified VL)) :=
  NNG_Observed136.producer VL (calls env) input (NNG_Projection136.output p) events a obs env

theorem producer_tree {H W : Type} (VL : RSL.VLib) (p : NNG_Projection136.Representation VL H)
    (calls : RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    producer VL p calls input events a obs env =
      NNG_Observed136.observation (NNG_Projection136.output p) (events env)
        (NNG_FinishTree.tree (calls env) (input a obs env)) :=
  NNG_Observed136.producer_tree VL (calls env) input (NNG_Projection136.output p) events a obs env
#print axioms producer_tree

theorem actual_emitted {H W : Type} (VL : RSL.VLib) (p : NNG_Projection136.Representation VL H)
    (calls : RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    RSL.Spec.map (NNG_Projection136.output p)
      (interpret events (NNG_FinishTree.tree (calls env) (input a obs env)))
        env (producer VL p calls input events a obs env) :=
  NNG_InterpretProjection.actual_emitted VL (calls env) input (NNG_Projection136.output p) events a obs env
#print axioms actual_emitted

/-- Canonical rev3 target, with Env-dependent source calls and a fixed,
field-by-field output representation. It is not a candidate theorem yet. -/
def Target {H W : Type} (VL : RSL.VLib) (p : NNG_Projection136.Representation VL H)
    (calls : RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) : Prop :=
  RSL.TX1_136.RowSpec_136 VL (producer VL p calls input events)
end AspisR1.NNG_EnvObserved136
