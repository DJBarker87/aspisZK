-- Aspis translatability pass (statement worker): two definitions of the Lean library that the second
-- tool pair's Aeneas (0d21a9ec) emits against and the R1 (L187) library does not have. Copied from the
-- Aeneas source beside that binary (codex-pc-prov-p4x-20261110/src/aeneas/backends/lean), attributes
-- and lemmas omitted:
--   Std/Core/CoreResult.lean sha256 3ec2fd63a51a5cc01cf81da0e18d129670a5b5da4c93c2c1703c6af6f7ab1c0f (Result.map)
--   Std/SliceIter.lean       sha256 9958f6bd9ba21f80b400314c6cad5bf4c7dac01af89892c2dfcd4dbd786b18dc (IteratorSliceIter.next_back)
-- One departure from the copied text: the truncated slice is built with the subtype constructor,
-- because the R1 library has no `Slice.from` (the probe's shim made the same change for `Array.from`).
-- Used ONLY to test whether emitted definitions elaborate; nothing is proved here about them.
import Aeneas
open Aeneas Aeneas.Std Result
namespace Aeneas.Std

def core.result.Result.map {T E U F : Type _} (fnOnce : core.ops.function.FnOnce F T U)
  (x : core.result.Result T E) (f : F) : Std.Result (core.result.Result U E) :=
  match x with
  | .Ok value => do
      let mapped ← fnOnce.call_once f value
      ok (.Ok mapped)
  | .Err error => ok (.Err error)

def core.slice.iter.IteratorSliceIter.next_back
  {T : Type _} (it : core.slice.iter.Iter T) : Result ((Option T) × (core.slice.iter.Iter T)) :=
  if h : it.i < it.slice.val.length then
    let n := it.slice.val.length - 1
    let x := it.slice[n]'(by scalar_tac)
    let s : Slice T := ⟨it.slice.val.take n, by scalar_tac⟩
    ok (some x, { it with slice := s })
  else ok (none, it)

end Aeneas.Std
