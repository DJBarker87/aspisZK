import FIq_Native14
import FIq_Carriers
set_option autoImplicit false
namespace AspisR1.FIq_Terminal
open Aeneas Aeneas.Std Result FIq_Carriers
abbrev B := AspisR1PublicPreparation.FinishModel.Boundaries
abbrev Error := AspisR1PublicPreparation.aspis_core.state_only_prefix.r0.Error

def fromError : FIq_Native.state_only_prefix.r0.Error → Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag a => .Tag a | .Length a => .Length a
  | .NonCanonical a b => .NonCanonical a b | .Boundary a => .Boundary a
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public

/-- Complete retained terminal computation. Only coordinate/record carriers are
converted; all composition, Poseidon, copy, equality and error branches execute. -/
def terminal (pub : Public) (claims : Array (Array MQ 29#usize) 3#usize)
    (alpha : Array MQ 10#usize) (c : AspisR1PublicPreparation.r1_wire.Challenges) :
    Result (core.result.Result MQ Error) := do
  let r ← FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
    (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c)
  match r with
  | .Ok q => ok (.Ok (fromQ q))
  | .Err e => ok (.Err (fromError e))

def install (b : B) : B := {b with terminal:=terminal}

theorem reached (pub : Public) (claims : Array (Array MQ 29#usize) 3#usize)
    (alpha : Array MQ 10#usize) (c : AspisR1PublicPreparation.r1_wire.Challenges)
    (out : MQ) (run : terminal pub claims alpha c=ok (.Ok out)) :
    ∃ native, FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c)=ok (.Ok native) ∧
      fromQ native=out := by
  unfold terminal at run
  cases h : FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c) with
  | fail e => simp only [h,bind_tc_fail] at run;cases run
  | div => simp only [h,bind_tc_div] at run;cases run
  | ok r =>
    simp only [h,bind_tc_ok] at run
    cases r with
    | Err e => cases run
    | Ok q => exact ⟨q,rfl,core.result.Result.Ok.inj (Result.ok.inj run)⟩

theorem fixed (b : B) : (install b).terminal=terminal := rfl
#print axioms FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
#print axioms reached
#print axioms fixed
end AspisR1.FIq_Terminal
