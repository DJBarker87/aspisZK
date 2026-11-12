-- Aspis translatability pass (verifier crate and program adapter): library definitions that the second tool pair's
-- Aeneas (0d21a9ec) emits against and that the R1 (L187) library does not have under these names. The first five are
-- those of extraction-probe/lean/AspisXPNewLib.lean (see the header kept below). Two more are added here, copied from
-- the same Aeneas source tree (attribute lists omitted):
--   Std/Slice.lean            sha256 1072c7667bbe7c926c1b0a4e96baad50ff2b47c5e181307736ceacd1d2212465  (SliceIndex for RangeFull)
--   Std/Array/ArraySlice.lean sha256 57d2d3bd653f3bd08c01874fbc1e5600bdd0cf54fb03371755db37d9bc0e0575  (TryFrom<&mut [T]> for &mut [T; N])
--   Std/Alloc/Alloc.lean      sha256 ebbce4a4d78701228d7edd041b5967e825ddc12b068d4a90a913754eff78e673  (the type alloc.alloc.Global only)
--   Std/Alloc/Vec.lean        sha256 4424fd5c2692fd2f970bccf7ffbe4e873fe09094705095c720838159bca55701  (Vec.is_empty only)
-- They are needed by fused::base_lanes_tight and by the adapter's stage2 (`&mut v[..]` and the conversion of a mutable
-- slice to a mutable array reference). Used ONLY to test whether emitted definitions elaborate.
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
namespace AspisTPNewLib

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

/-- The global allocator type (Std/Alloc/Alloc.lean of the second pair's library: `inductive alloc.alloc.Global where | mk`).
    The emission passes it as the allocator argument of `Vec::into_boxed_slice` (used by `r1_semantic::claims`). -/
inductive alloc.alloc.Global where | mk

/-- `Vec::is_empty` (Std/Alloc/Vec.lean of the second pair's library: `ok (v.length = 0)`); used by
    `QueryGeometry::for_range`. -/
def alloc.vec.Vec.is_empty {α : Type u} (v : alloc.vec.Vec α) : Result Bool := ok (decide (v.val.length = 0))

/-! ## `SliceIndex<RangeFull, [T]>`: indexing a slice with `..` yields the whole slice. -/
/-- `core::ops::RangeFull` (the R1 library has no such name; the emission passes `()` for its value). -/
def core.ops.range.RangeFull := Unit

def core.slice.index.SliceIndexRangeFullSlice.get
  {T : Type _} (_ : core.ops.range.RangeFull) (s : Slice T) : Result (Option (Slice T)) :=
  ok (some s)

def core.slice.index.SliceIndexRangeFullSlice.get_mut
  {T : Type _} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  ok (some s, fun s' => match s' with | some updated => updated | none => s)

def core.slice.index.SliceIndexRangeFullSlice.index
  {T : Type _} (_ : core.ops.range.RangeFull) (s : Slice T) : Result (Slice T) :=
  ok s

def core.slice.index.SliceIndexRangeFullSlice.index_mut
  {T : Type _} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result (Slice T × (Slice T → Slice T)) :=
  ok (s, fun updated => updated)

def core.slice.index.SliceIndexRangeFullSlice (T : Type _) :
  core.slice.index.SliceIndex core.ops.range.RangeFull (Slice T) (Slice T) := {
  sealedInst := {}
  get := core.slice.index.SliceIndexRangeFullSlice.get
  get_mut := core.slice.index.SliceIndexRangeFullSlice.get_mut
  get_unchecked := fun _ _ => fail .undef
  get_unchecked_mut := fun _ _ => fail .undef
  index := core.slice.index.SliceIndexRangeFullSlice.index
  index_mut := core.slice.index.SliceIndexRangeFullSlice.index_mut
}

/-- `TryFrom<&mut [T]> for &mut [T; N]`: the array view and the function that writes it back. -/
def core.array.TryFromMutArraySlice.try_from
  {T : Type _} (N : Usize) (s : Slice T) :
  Result (
    core.result.Result (Array T N) core.array.TryFromSliceError ×
    (core.result.Result (Array T N) core.array.TryFromSliceError → Slice T)) :=
  if h: s.len = N then
    let back (a : core.result.Result (Array T N) core.array.TryFromSliceError) : Slice T :=
      match a with
      | .Ok a => ⟨ a.val, by scalar_tac ⟩
      | _ => s
    ok ((.Ok ⟨ s.val, by scalar_tac ⟩, back))
  else ok ((.Err (), fun _ => s))

end AspisTPNewLib
