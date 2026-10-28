import JFw_Values
import RPz7_PSem_RowStep
import RPz7_PSem_Iterator
set_option autoImplicit false
namespace AspisR1.JFw_Row
open Aeneas Aeneas.Std Result WP ControlFlow
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

def runRow (input out : Slice U8) (nextRow row : U8) (size src dst : Usize) := do
  let i ← dst + 5#usize
  let (s, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) out {start := dst, «end» := i}
  let i1 ← src + 5#usize
  let s1 ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) input {start := src, «end» := i1}
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let b ← compact.compact_row row
  if b then
    let half ← size / 2#usize
    let sourceEnd ← i1 + half
    let payload ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) input {start := i1, «end» := sourceEnd}
    let destEnd ← i + size
    let (window, back1) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (back s2) {start := i, «end» := destEnd}
    let (status, updated) ← expandValues payload window
    let cf ← core.result.Result.Insts.CoreOpsTry.branch status
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let sourceNext ← i1 + half
      ok (cont (iter nextRow, back1 updated, sourceNext, destEnd))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame compact.CodecError) residual
      ok (done (r,back1 updated))
  else
    let destEnd ← i + size
    let (window, back1) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (back s2) {start := i, «end» := destEnd}
    let sourceEnd ← i1 + size
    let payload ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) input {start := i1, «end» := sourceEnd}
    let updated ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window payload
    ok (cont (iter nextRow,back1 updated,sourceEnd,destEnd))

theorem factor (input out : Slice U8) (row nextRow tag : U8) (size src dst : Usize)
    (bound : row.val < 27) (next : nextRow.val = row.val+1)
    (shape : r1_wire.row_shape row = ok (some (tag,size))) :
    compact.expand_semantic_loop.body nativeValues input (iter row) out src dst =
      runRow input out nextRow row size src dst := by
  unfold compact.expand_semantic_loop.body
  rw [next_row row nextRow bound next]
  simp only [bind_tc_ok]
  change (do
    let o1 ← r1_wire.row_shape row
    _) = _
  rw [shape]
  rfl


 theorem spec (input out : Slice U8) (row nextRow tag : U8) (size src dst : Usize)
    (bound : row.val < 27) (next : nextRow.val = row.val+1)
    (shape : r1_wire.row_shape row = ok (some (tag,size)))
    (sizeBound : size.val ≤ 3712) (aligned : size.val % 32 = 0)
    (inputBound : src.val+5+(if 14 ≤ row.val then size.val/2 else size.val) ≤ input.length)
    (outBound : dst.val+5+size.val ≤ out.length)
    (smallInput : input.length ≤ 20000) (smallOut : out.length ≤ 20000) :
    compact.expand_semantic_loop.body nativeValues input (iter row) out src dst
      ⦃ result => ∃ updated nextSrc nextDst,
        result = .cont (iter nextRow,updated,nextSrc,nextDst) ∧
        nextSrc.val = src.val+5+(if 14 ≤ row.val then size.val/2 else size.val) ∧
        nextDst.val = dst.val+5+size.val ⦄ := by
  rw [factor input out row nextRow tag size src dst bound next shape]
  unfold runRow compact.compact_row
  step* <;> try scalar_tac
  all_goals scalar_tac_preprocess
  all_goals simp_all [core.result.Result.Insts.CoreOpsTry.branch,Slice.setSlice!_length]
  all_goals scalar_tac

#print axioms factor

#print axioms spec
end AspisR1.JFw_Row
