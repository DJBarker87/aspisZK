import ToBytesP6StepsV3
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace P6ToBytes.ActiveBodyV11
open P6ToBytes.Steps AspisR1WideToBytesSource

theorem copy4 (chunk : Slice Std.U8) (h : chunk.val.length = 4) (w : Std.U32) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 chunk
      (Array.to_slice (core.num.U32.to_le_bytes w)) =
      .ok (Array.to_slice (core.num.U32.to_le_bytes w)) := by
  simp [core.slice.Slice.copy_from_slice, Array.to_slice, Slice.len, h,
    u32BytesLen, UScalar.ofNatCore_val_eq]

theorem copy4_any (chunk src : Slice Std.U8)
    (hc : chunk.val.length = 4) (hs : src.val.length = 4) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 chunk src = .ok src := by
  simp [core.slice.Slice.copy_from_slice, Slice.len, hc, hs,
    UScalar.ofNatCore_val_eq]

theorem body_progress (x : field.wide_exact.WideExact) (i : Nat)
    (c : ChunkIt) (d : LimbIt) (bk : Back)
    (hsource : c.source.val.length = 32)
    (hsize : c.chunkSize.val = 4)
    (hcc : c.cursor = 4*i)
    (hdata : d.data = sourceLimbs x)
    (hdc : d.cursor = i)
    (hi : i < 8) :
    ∃ c' d' bk',
      step ((⟨c,d⟩ : Zip), bk) = .ok (.cont ((⟨c',d'⟩ : Zip),bk')) ∧
      d'.data = d.data ∧ c'.cursor = 4*(i+1) ∧ d'.cursor = i+1 ∧
      c'.source = c.source ∧ c'.chunkSize = c.chunkSize := by
  have hchunkLen : (List.take 4 (List.drop (4*i) c.source.val)).length = 4 := by
    simp [List.length_take, List.length_drop, hsource]
    omega
  have hchunkActive : 4*i < 32 ∧ 4*i ≤ 28 := by omega
  have hlimbActive : i < (sourceLimbs x).length := by
    simp [sourceLimbs]
    omega
  simp [step, lift, bind_tc_ok, field.wide_exact.WideExact.to_le_bytes_loop.body,
    P6ToBytes.StdModel.zipNext,
    P6ToBytes.StdModel.MutableIterator.zip.trait_default,
    P6ToBytes.StdModel.MutableIterator,
    Aeneas.Std.core.slice.Slice.chunks_exact_mut,
    Aeneas.Std.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next,
    Aeneas.Std.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    P6ToBytes.ActiveBodyV11.copy4, Slice.len,
    u32BytesLen, UScalar.ofNatCore_val_eq, hsource, hsize, hcc, hdata, hdc, hi,
    hchunkLen, hchunkActive, hlimbActive, List.length_drop, List.length_take] <;> omega

#print axioms body_progress
end P6ToBytes.ActiveBodyV11
