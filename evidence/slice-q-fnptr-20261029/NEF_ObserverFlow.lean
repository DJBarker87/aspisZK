import NEF_ExtractedObserver
set_option autoImplicit false
namespace NEF_ObserverFlow
/-- Labels follow the finite source inventory, without making a claim about
unreached paths or accepting an externally injected library Observer. -/
inductive Site where
  | programTx1 | programTx2 | tx1 | tx2 | tx2Authenticated | tx2Common
  | prepare | queryLoop | queryValues | finishRelation | semantic | semanticFinish
  | verifierMark | semanticMark

/-- A source-forwarding step transports the parameter verbatim. The Python
certificate checks precisely this syntax, roots and complete occurrence set. -/
inductive Flow {Callback : Type} : Site → Option Callback → Prop where
  | tx1 : Flow .programTx1 none
  | tx2 : Flow .programTx2 none
  | forward {src dst value} : Flow src value → Flow dst value

theorem no_injection {Callback : Type} (site : Site) (value : Option Callback)
    (flow : Flow site value) : value = none := by
  induction flow with
  | tx1 => rfl
  | tx2 => rfl
  | forward _ ih => exact ih

/-- Every prefix, repeated loop edge and early-stop prefix preserves None. -/
inductive Path {Callback : Type} : Option Callback → List Site → Option Callback → Prop where
  | nil (value) : Path value [] value
  | step {before after sites site} : Path before sites after → Path before (site :: sites) after

theorem path_value {Callback : Type} (before after : Option Callback) (sites : List Site)
    (path : Path before sites after) : after = before := by
  induction path with
  | nil => rfl
  | step _ ih => exact ih

theorem reached_none {Callback : Type} (after : Option Callback) (sites : List Site)
    (path : Path none sites after) : after = none := path_value none after sites path
#print axioms no_injection
#print axioms path_value
#print axioms reached_none
end NEF_ObserverFlow
