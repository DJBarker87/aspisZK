import S2SdkOwnedTypesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS2SdkIterator
/-- [aspis_s126_sdk_iterator_reference::DataPointer]
    Source: 'src/lib.rs', lines 4:0-4:56
    Visibility: public -/
structure DataPointer where
  slot : Std.Usize
  offset : Std.Usize

/-- [aspis_s126_sdk_iterator_reference::SourceIterator]
    Source: 'src/lib.rs', lines 6:0-6:74
    Visibility: public -/
structure SourceIterator where
  ptr : DataPointer
  end_or_len : DataPointer

/-- [aspis_s126_sdk_iterator_reference::source_begin]:
    Source: 'src/lib.rs', lines 7:0-9:1
    Visibility: public -/
def source_begin
  (sdk : AspisS2OwnedStage1.SdkReference.OwnedSdk) (slot : Std.Usize) :
  Result SourceIterator
  := do
  let odc ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      AspisS2OwnedStage1.SdkReference.OwnedDataCell) sdk.data_cells slot
  let i := alloc.vec.Vec.len odc.bytes
  ok
    { ptr := { slot, offset := 0#usize }, end_or_len := { slot, offset := i } }

/-- [aspis_s126_sdk_iterator_reference::source_next]:
    Source: 'src/lib.rs', lines 10:0-18:1
    Visibility: public -/
def source_next
  (sdk : AspisS2OwnedStage1.SdkReference.OwnedSdk) (iter : SourceIterator) :
  Result ((Option Std.U8) × SourceIterator)
  := do
  massert (iter.ptr.slot = iter.end_or_len.slot)
  massert (iter.ptr.offset <= iter.end_or_len.offset)
  let odc ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      AspisS2OwnedStage1.SdkReference.OwnedDataCell) sdk.data_cells iter.ptr.slot
  let i := alloc.vec.Vec.len odc.bytes
  massert (iter.end_or_len.offset <= i)
  if iter.ptr.offset = iter.end_or_len.offset
  then ok (none, iter)
  else
    let byte ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U8)
        odc.bytes iter.ptr.offset
    let i1 ← iter.ptr.offset + 1#usize
    ok (some byte, { iter with ptr := { iter.ptr with offset := i1 } })

#print axioms source_begin
#print axioms source_next
end AspisS2SdkIterator
