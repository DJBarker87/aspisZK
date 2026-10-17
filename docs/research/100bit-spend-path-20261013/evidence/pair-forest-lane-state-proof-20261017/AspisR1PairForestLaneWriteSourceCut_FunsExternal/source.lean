-- Source model of Rust std::option::Option<T>::eq.
-- Pin: rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65),
-- library/core/src/option.rs:2438-2452; full file SHA-256
-- 7cf61204b05d98a95bc2e322d5fbfc1f4f91505109971917d9a7fb47151c50e6.
import Aeneas
import AspisR1PairForestLaneWriteSourceCut.Types
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisR1PairForestLaneWriteSourceCut

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
    {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T)
    (self other : Option T) : Result Bool :=
  match self, other with
  | none, none => ok true
  | some left, some right => cmpPartialEqInst.eq left right
  | none, some _ => ok false
  | some _, none => ok false

end AspisR1PairForestLaneWriteSourceCut
