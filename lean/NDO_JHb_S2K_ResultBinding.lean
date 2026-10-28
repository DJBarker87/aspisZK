import NDO_JHb_S2K_ResultWholeNative

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultBinding
open AspisR1TerminalDecoder Equality StatementAdmission StatementChecks ResultAdmission
open pool_v1.pair_forest_terminal pool_v1.pair_terminal

theorem byte_array_ne_self {n : Usize} (a : Array U8 n) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a = ok false :=
  array_ne_self _ u8_ne_self a

theorem digest_ne_self {n : Usize} (a : Array aspis_core.field.M31 n) :
    core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a a = ok false :=
  array_ne_self _ m31_ne_self a

theorem afterstate_self (a : PoolV1PairVerifiedAfterstateV1) :
    PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq a a = ok true := by
  have root := array_self _ m31_ne_self a.next_root
  have frontier := array_self (Array.Insts.CoreCmpPartialEqArray 8#usize
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31)
    (fun xs => digest_ne_self xs) a.next_frontier
  simp only [PoolV1PairVerifiedAfterstateV1.Insts.CoreCmpPartialEqPoolV1PairVerifiedAfterstateV1.eq,
    if_pos rfl,root,bind_tc_ok]
  exact frontier

theorem validated (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s (value s) = ok (.Ok ()) := by
  have valid := ResultAdmission.validated s accepted
  simp only [validate_pool_v1_pair_forest_terminal_result_against_statement_v1,
    accepted,valid,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  cases s <;> simp [value,kind,common,nullifier,
    PoolV1PairForestTerminalStatementV1.common,
    PoolV1PairForestTerminalStatementV1.transition_kind,
    PoolV1PairForestTerminalStatementV1.nullifier,
    core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    pool_v1.historical_anchor.PoolV1TransitionKind.Insts.CoreCmpPartialEqPoolV1TransitionKind.eq,
    byte_array_ne_self,digest_ne_self,afterstate_self]

#print axioms byte_array_ne_self
#print axioms digest_ne_self
#print axioms afterstate_self
#print axioms validated
end AspisR1.S2K.ResultBinding
