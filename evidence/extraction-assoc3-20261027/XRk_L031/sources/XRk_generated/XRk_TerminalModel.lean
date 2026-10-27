import XRk_MaskModel
import FIq_Terminal
open Aeneas Aeneas.Std Result ControlFlow Error
open XRk_Release XRk_FieldExternal
/- Read-only reuse of the coherent complete native terminal (FIq_Terminal),
   with explicit release/cohort carriers. This does not prove its source P6
   or claim that the old public carrier is the shipped physical public bytes. -/
def XRk_oldChallenges (c : aspis_core.state_only_prefix.r0.Challenges) :
    AspisR1PublicPreparation.r1_wire.Challenges :=
  {lambda := oldQ c.lambda, chi := oldQ c.chi, theta := oldQ c.theta,
   zc := AspisR1.FIq_Carriers.mapArray oldQ c.zc, mu := oldQ c.mu, eta := oldQ c.eta}
def XRk_newError : AspisR1PublicPreparation.aspis_core.state_only_prefix.r0.Error → aspis_core.state_only_prefix.r0.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag a => .Tag a | .Length a => .Length a
  | .NonCanonical a b => .NonCanonical a b | .Boundary a => .Boundary a
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public
noncomputable def aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
    (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (alpha : Array aspis_core.field.QM31 10#usize) (c : aspis_core.state_only_prefix.r0.Challenges) :
    Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error) := do
  let r ← AspisR1.FIq_Terminal.terminal (XRk_oldPublic p)
    (AspisR1.FIq_Carriers.mapArray (AspisR1.FIq_Carriers.mapArray oldQ) claims)
    (AspisR1.FIq_Carriers.mapArray oldQ alpha) (XRk_oldChallenges c)
  match r with
  | .Ok q => ok (.Ok (newQ q))
  | .Err e => ok (.Err (XRk_newError e))
#print axioms aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
