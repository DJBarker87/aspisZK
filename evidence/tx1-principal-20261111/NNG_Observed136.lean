import NNG_TreeEmission
import RSL_TX1_136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Observed136
open Aeneas Aeneas.Std Result NNG_Emitted NMT_CallTree

/-- Outer failure is an abort; an inner Rust Err remains a returned value.
Divergence is separate. There is no post-stop state. -/
def exit {A B : Type} (decode : A → B) : Result A → RSL.Exit B
  | .ok a => .ret (decode a)
  | .fail _ => .abort
  | .div => .diverge

/-- The trace retains SAME typed arguments and full child replies. Only the
CLOSED-child trace interpretation may supply the events attached to a call. -/
def observation {A B : Type} (decode : A → B)
    (events : NMT_CallTree.Event → List RSL.Event) (code : Code A) : RSL.Obs B :=
  let out := run code
  ⟨exit decode out.1, out.2.flatMap events⟩

/-- This is the producer used by the row target: its value comes from the
fresh emitted function, and its effects from that body's typed call trace. -/
def producer {H W : Type} (VL : RSL.VLib) (c : Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (decode : Output H → Except VL.WErr (RSL.Verified VL))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    RSL.Obs (Except VL.WErr (RSL.Verified VL)) :=
  let s := input a obs env
  ⟨exit decode (NNG_Emitted.emitted c s),
    (run (NNG_FinishTree.tree c s)).2.flatMap (events env)⟩

/-- No independent result or log is chosen by this observation adapter. -/
theorem producer_tree {H W : Type} (VL : RSL.VLib) (c : Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (decode : Output H → Except VL.WErr (RSL.Verified VL))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    producer VL c input decode events a obs env =
      observation decode (events env) (NNG_FinishTree.tree c (input a obs env)) := by
  change RSL.Obs.mk (exit decode (NNG_Emitted.emitted c (input a obs env))) _ =
    RSL.Obs.mk (exit decode (run (NNG_FinishTree.tree c (input a obs env))).1) _
  rw [run_result, NNG_TreeEmission.erase_tree]
#print axioms producer_tree

/-- Exact canonical target; it is a proposition, not a candidate theorem.
LIB supplies VL, the carrier interpretation and the CLOSED child trace laws. -/
def Target {H W : Type} (VL : RSL.VLib) (c : Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → Parent H W)
    (decode : Output H → Except VL.WErr (RSL.Verified VL))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) : Prop :=
  RSL.TX1_136.RowSpec_136 VL (producer VL c input decode events)
end AspisR1.NNG_Observed136
