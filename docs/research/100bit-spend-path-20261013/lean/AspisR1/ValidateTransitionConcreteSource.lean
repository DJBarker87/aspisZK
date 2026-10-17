import TerminalValidateTransitionEntryCarry
import Aeneas.Tactic.RustAttributes
import AspisR1TerminalValidator.FunsExternal

/-! Concrete ordered validator, sharing the proved loop/public/error owners.
The carry suffix is the adopted production bounded-carry migration. -/
set_option autoImplicit false
namespace AspisR1.ValidateTransitionConcreteSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open scoped AspisR1TerminalValidator

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T)
  (other : Option T) :
  Result Bool
  := do
  match self with
  | none => let other1 := read_discriminant other
            ok (other1 = 0#isize)
  | some l =>
    match other with
    | none => ok false
    | some r => cmpPartialEqInst.eq l r

@[reducible, rust_trait_impl
  "core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>"]
impl_def core.option.Option.Insts.CoreCmpPartialEqOption {T : Type}
  (cmpPartialEqInst : core.cmp.PartialEq T T) : core.cmp.PartialEq (Option T)
  (Option T) := {
  eq := core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption cmpPartialEqInst)
}

@[global_simps, irreducible]
def pool_v1.format.POOL_V1_TREE_DEPTH : Std.Usize := 20#usize

@[global_simps, irreducible]
def pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH : Std.Usize :=
  pool_v1.format.POOL_V1_TREE_DEPTH

@[global_simps, irreducible]
def pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY : Result Std.U64 :=
  1#u64 <<< pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH

def pool_v1.pair_forest_semantic_terminal.validate_transition
  (public1 : AspisR1TerminalValidateTransitionCandidate.EntryPublic) :
  Result (core.result.Result Unit
    AspisR1TerminalValidateTransitionCandidate.EntryError)
  := do
  let b ←
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      public1.transition.live_snapshot.pool public1.pool
  if b
  then
    ok (core.result.Result.Err
      AspisR1TerminalValidateTransitionCandidate.EntryInvalid)
  else
    let b1 ←
      core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
        public1.transition.live_snapshot.deployment_domain
        public1.deployment_domain
    if b1
    then
      ok (core.result.Result.Err
        AspisR1TerminalValidateTransitionCandidate.EntryInvalid)
    else
      if public1.transition.live_snapshot.sequence !=
        public1.transition.live_snapshot.next_pair_index
      then
        ok (core.result.Result.Err
          AspisR1TerminalValidateTransitionCandidate.EntryInvalid)
      else
        let i ← pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
        if public1.transition.live_snapshot.next_pair_index >= i
        then
          ok (core.result.Result.Err
            AspisR1TerminalValidateTransitionCandidate.EntryInvalid)
        else
          let o ←
            lift (U64.checked_add
              public1.transition.live_snapshot.next_pair_index 1#u64)
          let b2 ←
            core.cmp.PartialEq.ne.trait_default
              (core.option.Option.Insts.CoreCmpPartialEqOption
              core.cmp.PartialEqU64) o (some
              public1.transition.candidate_afterstate.next_pair_index)
          if b2
          then
            ok (core.result.Result.Err
              AspisR1TerminalValidateTransitionCandidate.EntryInvalid)
          else
            let carry ← AspisBoundedControl.bounded_carry
              public1.transition.live_snapshot.next_pair_index
            AspisR1TerminalValidateTransitionCandidate.validate_transition_loop
              public1 { start := 0#usize, «end» := 20#usize } carry

end AspisR1.ValidateTransitionConcreteSource
