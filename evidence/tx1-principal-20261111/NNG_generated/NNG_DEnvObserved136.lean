import NNG_InterpretProjection
import NNG_DProjectionLaws136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DEnvObserved136
open Aeneas Aeneas.Std Result NNG_Emitted NMT_CallTree NNG_Interpret136

/-- Per-input carrier maps may use the original semantic values as defaults
outside the proved raw domains. Calls are selected at the SAME actual Env,
so reservation and oracle replies remain universally quantified. -/
def producer {H W : Type} (VL : RSL.VLib)
    (project : RSL.TX1_136.Args VL → NNG_DProjection136.Representation VL H)
    (calls : RSL.TX1_136.Args VL → RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.TX1_136.Args VL → RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    RSL.Obs (Except VL.WErr (RSL.Verified VL)) :=
  NNG_Observed136.producer VL (calls a env) input (NNG_DProjection136.output (project a)) (events a) a obs env

theorem producer_tree {H W : Type} (VL : RSL.VLib)
    (project : RSL.TX1_136.Args VL → NNG_DProjection136.Representation VL H)
    (calls : RSL.TX1_136.Args VL → RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.TX1_136.Args VL → RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    producer VL project calls input events a obs env =
      NNG_Observed136.observation (NNG_DProjection136.output (project a)) (events a env)
        (NNG_FinishTree.tree (calls a env) (input a obs env)) :=
  NNG_Observed136.producer_tree VL (calls a env) input (NNG_DProjection136.output (project a)) (events a) a obs env
#print axioms producer_tree

/-- Exact canonical target. The caller's original semantic Prefix is retained
by the source fold; no global inverse of its provenance wrapper is required. -/
def Target {H W : Type} (VL : RSL.VLib)
    (project : RSL.TX1_136.Args VL → NNG_DProjection136.Representation VL H)
    (calls : RSL.TX1_136.Args VL → RSL.Env → Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (events : RSL.TX1_136.Args VL → RSL.Env → NMT_CallTree.Event → List RSL.Event) : Prop :=
  RSL.TX1_136.RowSpec_136 VL (producer VL project calls input events)
end AspisR1.NNG_DEnvObserved136
