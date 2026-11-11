-- Aspis extraction probe: five definitions of the Lean library that the second tool pair's Aeneas (0d21a9ec) emits
-- against, which the R1 (L187) library does not have under these names. Copied from the Aeneas source beside the
-- binary (codex-pc-prov-p4x-20261110/src/aeneas/backends/lean), attribute lists omitted:
--   Std/Core/Convert.lean    sha256 e258655835a72b3927bd2e2fb222467329b630d31f643ae26065be32ae6096ed  (branch, from_residual)
--   Std/Primitives.lean                                                                                (Never)
--   Std/Core/CoreResult.lean sha256 3ec2fd63a51a5cc01cf81da0e18d129670a5b5da4c93c2c1703c6af6f7ab1c0f  (map_err)
--   Std/Core/CoreOption.lean sha256 34568f540fbb757a44dfa83d665fef68d01c76bfb6f259954bfb6f65dc0e47c5  (ok_or)
--   Std/Array/FromFn.lean    sha256 18a00e016989a9ef23d29cfe26520b22803b3e26994a5847dacd09d0d86f5ad8  (from_fn)
-- The same device as the soundness lead's PCWN_NewLib (evidence/prov-p5e-20261110/PCWN_newlib_block.lean), which has the
-- first two. One departure from the copied text: the last line of from_fn builds the array with the subtype
-- constructor, because the R1 library has no `Array.from`. Used ONLY to test whether emitted definitions elaborate; nothing is proved here about these definitions.
import Aeneas
open Aeneas Aeneas.Std Result
namespace AspisXPNewLib

/-- The Never type in Rust -/
inductive Never where

def core.result.Result.Insts.CoreOpsTry.branch
  {T E : Type _} :
  core.result.Result T E →
    Std.Result (core.ops.control_flow.ControlFlow
      (core.result.Result Never E) T)
  | .Ok v => .ok (.Continue v)
  | .Err e => .ok (.Break (.Err e))

def core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  (T : Type _) {E F : Type _} (convertFromInst : core.convert.From F E)
  (r : core.result.Result Never E) : Std.Result (core.result.Result T F) :=
  match r with
  | .Ok x => x.casesOn
  | .Err e => do
      let v ← convertFromInst.from e
      .ok (.Err v)

def core.result.Result.map_err
  {T E F O : Type _} (fnOnce : core.ops.function.FnOnce O E F)
  (x : core.result.Result T E) (f : O) :
  Std.Result (core.result.Result T F) :=
  match x with
  | .Ok value => ok (.Ok value)
  | .Err error => do
      let mapped ← fnOnce.call_once f error
      ok (.Err mapped)

-- Second departure: the emission calls `ok_or` as a total function (it wraps the call in `lift`), so it is defined
-- here without the `Result` wrapper that the copied source file has.
def core.option.Option.ok_or {T E : Type _} (x : Option T) (e : E) :
  core.result.Result T E :=
  match x with
  | some value => .Ok value
  | none => .Err e

def core.array.from_fn {T F : Type u} (N : Usize) (inst : core.ops.function.FnMut F Usize T)
    (f : F) : Result (Array T N) := do
  let (v, _) ← StateT.run (Vector.ofFnM (m := StateT F Result) (n := N.val) fun i g =>
    inst.call_mut g (UScalar.ofNatCore i.val (by scalar_tac))) f
  ok ⟨ v.toList, by simp ⟩

end AspisXPNewLib
