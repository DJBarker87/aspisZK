import NHC_Hints.Types
open Aeneas Aeneas.Std Result
namespace NHC_Hints
/-- Standard Option elimination, implemented rather than assumed. -/
def core.option.Option.ok_or {T E : Type} (x : Option T) (e : E) : Result (Aeneas.Std.core.result.Result T E) :=
  ok (match x with | none => .Err e | some v => .Ok v)
/-- Frozen pair_forest.rs:110, exactly four hint bytes. -/
def pair_forest.POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES : Result Usize := ok 4#usize

theorem option_none {T E : Type} (e : E) :
    core.option.Option.ok_or (none : Option T) e = ok (.Err e) := rfl
#print axioms option_none

theorem option_some {T E : Type} (v : T) (e : E) :
    core.option.Option.ok_or (some v) e = ok (.Ok v) := rfl
#print axioms option_some

theorem hint_width : pair_forest.POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES = ok 4#usize := rfl
#print axioms hint_width
end NHC_Hints
