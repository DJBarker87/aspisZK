import R1Z.PV_RDCD5_V233
import R1Z.PV_DL_UpdateCarrier
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_UpdateSplit
open Aeneas Aeneas.Std Result PV_CBL_GenericArrayPower

/-- Cursor-recursive views and absolute windows name the same ordered blocks. -/
theorem views_range (n : Nat) (input : List U8) :
    PV_DL_UpdateViews.views n input =
      (List.range n).map (fun i => (input.drop (i*64)).take 64) := by
  apply List.ext_getElem
  · simp only [PV_DL_UpdateViews.count,List.length_map,List.length_range]
  · intro i hi hj
    have hn : i < n := by simpa only [PV_DL_UpdateViews.count] using hi
    have h := PV_DL_UpdateViews.coordinate n i input hn
    simp only [List.getElem?_eq_getElem hi,Option.some.injEq,Nat.mul_comm] at h
    simpa only [List.getElem_map,List.getElem_range,Nat.mul_comm] using h

/-- StorageBuild and BlockCodec recover the same typed storage, for every
64-byte block. Injectivity is used, rather than assuming byte equality suffices. -/
theorem storage_encoding (bytes : List U8) (hb : bytes.length = 64) :
    PV_DL_StorageBuild.build 6 (fun i => bytes[i]!) = PV_AL_BlockCodec.encode 6 bytes := by
  apply PV_RDCD5_BlockCarrier.flatten_injective 6
  rw [PV_DL_StorageBuild.reconstruct 6 bytes hb,PV_AL_BlockCodec.flatten_encode 6 bytes hb]

/-- Exact typed list, including count, order, and the GenericArray data tree. -/
theorem typed_batches (N : Type) (input : Slice U8) :
    PV_DL_UpdateCarrier.blockList N input.val = PV_AL_SplitCarrier.values N input := by
  unfold PV_DL_UpdateCarrier.blockList
  rw [views_range]
  simp only [List.map_map,PV_AL_SplitCarrier.values]
  apply List.map_congr_left
  intro i hi
  have hb := PV_CBL_SplitModel.block_length input.val 64 i (List.mem_range.mp hi)
  change (⟨PV_DL_StorageBuild.build 6 (fun j => (PV_CBL_SplitModel.block input.val 64 i)[j]!)⟩ :
    PV_AL_SplitCarrier.Block N) = PV_AL_SplitCarrier.encodeBlock N (PV_CBL_SplitModel.block input.val 64 i)
  unfold PV_AL_SplitCarrier.encodeBlock
  rw [storage_encoding _ hb]

/-- The full Result-valued update receives precisely the typed split carrier.
No purity, totality, per-block fold law, or extra callback premise is used. -/
theorem compression_instance {T N : Type}
    (update : T → PV_DL_UpdateCarrier.Blocks N → Result T) (state : T) (input : Slice U8) :
    PV_DL_UpdateCarrier.compress update state input.val =
      update state (PV_AL_SplitCarrier.blockSlice N input) := by
  rw [PV_DL_UpdateCarrier.compression_call update state input.val input.property]
  congr 1
  apply Subtype.ext
  exact typed_batches N input

#print axioms views_range
#print axioms storage_encoding
#print axioms typed_batches
#print axioms compression_instance
end R1Z.PV_RDCD5_UpdateSplit
