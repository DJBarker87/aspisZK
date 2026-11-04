import Lean
import NFY_Part023
import NFY_Part024
import NFY_Part034
import NFY_Part022
import NFY_Part020

-- BEGIN copied JFs_AfterstateHeader: lean/JFs_AfterstateHeader.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_AfterstateHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

def magic : Slice U8 := ⟨NFY_JFu_PublicMeta06.bytes.take 4,by simp [NFY_JFu_PublicMeta06.bytes];scalar_tac⟩
theorem magic_selected : NFY_JFu_PublicRange.segment 976 4 (by decide)=magic := by
  apply Subtype.ext
  exact NFY_JFt_LocalWindow.selected 976 16 0 4 (by decide) (by decide) _ NFY_JFu_PublicMeta06.selected

theorem magic_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC {start:=0#usize,«end»:=4#usize}=ok magic := by
  unfold POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC
  rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) magic magic=ok false := by rfl

theorem b4 : Slice.index_usize NFY_JFu_PublicRange.afterstate 4#usize=ok 1#u8 := by
  exact NFY_JFs_IndexWindow.source 976 688 16 (by decide) 4#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta06.bytes NFY_JFu_PublicMeta06.selected (by rfl)

theorem b5 : Slice.index_usize NFY_JFu_PublicRange.afterstate 5#usize=ok 1#u8 := by
  exact NFY_JFs_IndexWindow.source 976 688 16 (by decide) 5#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta06.bytes NFY_JFu_PublicMeta06.selected (by rfl)

theorem b6 : Slice.index_usize NFY_JFu_PublicRange.afterstate 6#usize=ok 1#u8 := by
  exact NFY_JFs_IndexWindow.source 976 688 16 (by decide) 6#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta06.bytes NFY_JFu_PublicMeta06.selected (by rfl)

theorem b7 : Slice.index_usize NFY_JFu_PublicRange.afterstate 7#usize=ok 1#u8 := by
  exact NFY_JFs_IndexWindow.source 976 688 16 (by decide) 7#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta06.bytes NFY_JFu_PublicMeta06.selected (by rfl)

#print axioms magic_selected
#print axioms magic_array
#print axioms magic_compare
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
end AspisR1.NFY_JFs_AfterstateHeader
-- END copied JFs_AfterstateHeader
-- BEGIN copied JFt_ExactArray: lean/JFt_ExactArray.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_ExactArray
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

theorem cast (N : Usize) (bytes : Slice U8) (arr : Array U8 N) (same : bytes.val=arr.val) :
    core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 bytes=ok (.Ok arr) := by
  have size : bytes.length=N.val := by change bytes.val.length=N.val;rw [same,arr.property]
  have spec : core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 bytes
      ⦃ out => out=.Ok arr ⦄ := by
    step*
    cases out with
    | Err e => exact False.elim (out_post size)
    | Ok value =>
      congr 1
      exact Subtype.ext (out_post.1.trans same)
  obtain ⟨out,call,equal⟩:=WP.spec_imp_exists spec
  rw [equal] at call
  exact call

theorem source (N : Usize) (bytes : Slice U8) (arr : Array U8 N) (same : bytes.val=arr.val) :
    pool_v1.pair_terminal.exact N bytes=ok (.Ok arr) := by
  unfold pool_v1.pair_terminal.exact
  rw [cast N bytes arr same]
  rfl

#print axioms cast
#print axioms source
end AspisR1.NFY_JFt_ExactArray
-- END copied JFt_ExactArray
-- BEGIN copied JFt_DigestInjective: lean/JFt_DigestInjective.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_DigestInjective
open Aeneas Aeneas.Std Result

theorem fromLEBytes_cast {b : BitVec 32} {bs : List Byte}
    (same : bs=b.toLEBytes) : (BitVec.fromLEBytes bs).cast (by rw [same];simp [BitVec.toLEBytes_length])=b := by
  cases same
  rw [BitVec.fromLEBytes_toLEBytes (by decide : 32%8=0)]
  simp

theorem from_to (x : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  have point : ∀ b : Byte,U8.bv (UScalar.mk b)=b := by intro b;rfl
  have map : List.map U8.bv (List.map UScalar.mk x.bv.toLEBytes)=x.bv.toLEBytes := by
    rw [List.map_map]
    simpa [Function.comp_def] using congrArg (fun f : Byte → Byte => List.map f x.bv.toLEBytes) (funext point)
  apply U32.bv_eq_imp_eq
  simp only [core.num.U32.from_le_bytes,core.num.U32.to_le_bytes]
  exact fromLEBytes_cast map

theorem word_length (x : U32) : (core.num.U32.to_le_bytes x).val.length=4 :=
  (core.num.U32.to_le_bytes x).property

@[simp] theorem take_word (x : U32) : (core.num.U32.to_le_bytes x).val.take 4=(core.num.U32.to_le_bytes x).val :=
  List.take_of_length_le (by rw [word_length])

theorem injective (a b : Array U32 8#usize)
    (same : AspisS6SourceCodec.DigestContents.chunks a=AspisS6SourceCodec.DigestContents.chunks b) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [a.property,b.property]
  · intro i ha hb
    have small : i<8 := by simpa only [a.property,show (8#usize).val=8 from rfl] using ha
    have selected:=congrArg (fun xs : List U8 => (xs.drop (4*i)).take 4) same
    have word : (core.num.U32.to_le_bytes a.val[i]).val=(core.num.U32.to_le_bytes b.val[i]).val := by
      interval_cases i <;>
        simpa [AspisS6SourceCodec.DigestContents.chunks,word_length,List.drop_append,List.take_append] using selected
    have arrays : core.num.U32.to_le_bytes a.val[i]=core.num.U32.to_le_bytes b.val[i] := Subtype.ext word
    simpa only [from_to] using congrArg core.num.U32.from_le_bytes arrays

#print axioms fromLEBytes_cast
#print axioms from_to
#print axioms word_length
#print axioms take_word
#print axioms injective
end AspisR1.NFY_JFt_DigestInjective
-- END copied JFt_DigestInjective
-- BEGIN copied JFt_DigestArray: lean/JFt_DigestArray.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_DigestArray
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem shared (bytes : Slice U8) (arr : Array U8 32#usize) (same : bytes.val=arr.val) :
    core.array.TryFromSharedArraySlice.try_from 32#usize bytes=ok (.Ok arr) := by
  have size : Slice.len bytes=32#usize := by
    have h : bytes.length=32 := by change bytes.val.length=32;rw [same,arr.property];rfl
    scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dif_pos size]
  apply congrArg ok
  apply congrArg core.result.Result.Ok
  exact Subtype.ext same

theorem source (bytes : Slice U8) (arr : Array U8 32#usize) (same : bytes.val=arr.val)
    (digest : Array U32 8#usize)
    (call : AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok digest)) :
    atomic_statement.decode_digest_canonical arr=ok (.Ok digest) := by
  unfold AspisS6NativeSnapshotReadDigest.read_digest at call
  rw [shared bytes arr same] at call
  simpa only [bind_tc_ok,atomic_statement.unwrap_fixed_slice] using call

#print axioms shared
#print axioms source
end AspisR1.NFY_JFt_DigestArray
-- END copied JFt_DigestArray
-- BEGIN copied JFt_Digest22: lean/JFt_Digest22.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest22
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [67464615#u32,2144218473#u32,1164697229#u32,2001687059#u32,97906516#u32,820214304#u32,716699029#u32,134105794#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest22.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest22.window
    NFY_JFu_PublicDigest22.length NFY_JFu_PublicDigest22.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest22.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest22.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 992 32 (by decide)=NFY_JFu_PublicDigest22.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest22.window]
  exact NFY_JFu_PublicDigest22.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 992 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest22
-- END copied JFt_Digest22
-- BEGIN copied JFt_Digest23: lean/JFt_Digest23.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest23
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1438900896#u32,782233260#u32,1544844157#u32,891350894#u32,986827501#u32,300047813#u32,266092546#u32,1155026732#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest23.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest23.window
    NFY_JFu_PublicDigest23.length NFY_JFu_PublicDigest23.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest23.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest23.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1024 32 (by decide)=NFY_JFu_PublicDigest23.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest23.window]
  exact NFY_JFu_PublicDigest23.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1024 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest23
-- END copied JFt_Digest23
-- BEGIN copied JFt_Digest24: lean/JFt_Digest24.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest24
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [248012357#u32,194341198#u32,430781749#u32,501414171#u32,630694870#u32,1921243919#u32,1220508734#u32,1000843895#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest24.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest24.window
    NFY_JFu_PublicDigest24.length NFY_JFu_PublicDigest24.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest24.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest24.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1056 32 (by decide)=NFY_JFu_PublicDigest24.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest24.window]
  exact NFY_JFu_PublicDigest24.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1056 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest24
-- END copied JFt_Digest24
-- BEGIN copied JFt_Digest25: lean/JFt_Digest25.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest25
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [560027647#u32,109760138#u32,2064904093#u32,345398497#u32,1214731266#u32,366495038#u32,459312327#u32,480913462#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest25.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest25.window
    NFY_JFu_PublicDigest25.length NFY_JFu_PublicDigest25.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest25.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest25.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1088 32 (by decide)=NFY_JFu_PublicDigest25.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest25.window]
  exact NFY_JFu_PublicDigest25.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1088 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest25
-- END copied JFt_Digest25
-- BEGIN copied JFt_Digest26: lean/JFt_Digest26.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest26
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1603344092#u32,1242405009#u32,1153352827#u32,393697509#u32,714169239#u32,2094351560#u32,55834509#u32,664305674#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest26.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest26.window
    NFY_JFu_PublicDigest26.length NFY_JFu_PublicDigest26.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest26.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest26.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1120 32 (by decide)=NFY_JFu_PublicDigest26.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest26.window]
  exact NFY_JFu_PublicDigest26.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1120 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest26
-- END copied JFt_Digest26
-- BEGIN copied JFt_Digest27: lean/JFt_Digest27.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest27
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1410054462#u32,673771449#u32,940847521#u32,274330358#u32,1719505495#u32,1690439941#u32,203201419#u32,1855504616#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest27.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest27.window
    NFY_JFu_PublicDigest27.length NFY_JFu_PublicDigest27.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest27.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest27.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1152 32 (by decide)=NFY_JFu_PublicDigest27.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest27.window]
  exact NFY_JFu_PublicDigest27.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1152 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest27
-- END copied JFt_Digest27
-- BEGIN copied JFt_Digest28: lean/JFt_Digest28.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest28
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1442759752#u32,1540325866#u32,188964047#u32,101815282#u32,1883549730#u32,1774537487#u32,1306717763#u32,561084592#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest28.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest28.window
    NFY_JFu_PublicDigest28.length NFY_JFu_PublicDigest28.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest28.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest28.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1184 32 (by decide)=NFY_JFu_PublicDigest28.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest28.window]
  exact NFY_JFu_PublicDigest28.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1184 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest28
-- END copied JFt_Digest28
-- BEGIN copied JFt_Digest29: lean/JFt_Digest29.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest29
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [244193611#u32,984304317#u32,1467689208#u32,2063463197#u32,1766003332#u32,1300835127#u32,1578947755#u32,745931587#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest29.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest29.window
    NFY_JFu_PublicDigest29.length NFY_JFu_PublicDigest29.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest29.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest29.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1216 32 (by decide)=NFY_JFu_PublicDigest29.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest29.window]
  exact NFY_JFu_PublicDigest29.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1216 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest29
-- END copied JFt_Digest29
-- BEGIN copied JFt_Digest30: lean/JFt_Digest30.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest30
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [673192756#u32,38070812#u32,1453532835#u32,1340577407#u32,368420458#u32,1834405704#u32,270061815#u32,711700631#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest30.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest30.window
    NFY_JFu_PublicDigest30.length NFY_JFu_PublicDigest30.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest30.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest30.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1248 32 (by decide)=NFY_JFu_PublicDigest30.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest30.window]
  exact NFY_JFu_PublicDigest30.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1248 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest30
-- END copied JFt_Digest30
-- BEGIN copied JFt_Digest31: lean/JFt_Digest31.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest31
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [27092219#u32,1272373356#u32,998194489#u32,1458413288#u32,887470405#u32,1204987730#u32,864453460#u32,553704718#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest31.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest31.window
    NFY_JFu_PublicDigest31.length NFY_JFu_PublicDigest31.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest31.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest31.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1280 32 (by decide)=NFY_JFu_PublicDigest31.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest31.window]
  exact NFY_JFu_PublicDigest31.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1280 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest31
-- END copied JFt_Digest31
-- BEGIN copied JFt_Digest32: lean/JFt_Digest32.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest32
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1972918328#u32,1234090299#u32,977162835#u32,1704494754#u32,1617603773#u32,1819200880#u32,906453206#u32,1653526885#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest32.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest32.window
    NFY_JFu_PublicDigest32.length NFY_JFu_PublicDigest32.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest32.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest32.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1312 32 (by decide)=NFY_JFu_PublicDigest32.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest32.window]
  exact NFY_JFu_PublicDigest32.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1312 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest32
-- END copied JFt_Digest32
-- BEGIN copied JFt_Digest33: lean/JFt_Digest33.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest33
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [418360492#u32,472096212#u32,871749117#u32,98906847#u32,2026788776#u32,1504737042#u32,407274798#u32,1800828893#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest33.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest33.window
    NFY_JFu_PublicDigest33.length NFY_JFu_PublicDigest33.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest33.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest33.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1344 32 (by decide)=NFY_JFu_PublicDigest33.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest33.window]
  exact NFY_JFu_PublicDigest33.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1344 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest33
-- END copied JFt_Digest33
-- BEGIN copied JFt_Digest34: lean/JFt_Digest34.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest34
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [986339640#u32,660349625#u32,1012157959#u32,454024326#u32,987656904#u32,622864739#u32,1150440730#u32,1280042062#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest34.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest34.window
    NFY_JFu_PublicDigest34.length NFY_JFu_PublicDigest34.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest34.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest34.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1376 32 (by decide)=NFY_JFu_PublicDigest34.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest34.window]
  exact NFY_JFu_PublicDigest34.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1376 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest34
-- END copied JFt_Digest34
-- BEGIN copied JFt_Digest35: lean/JFt_Digest35.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest35
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [2118470693#u32,1706590589#u32,2128512933#u32,167263577#u32,409542414#u32,1323179656#u32,1880070613#u32,2053396184#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest35.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest35.window
    NFY_JFu_PublicDigest35.length NFY_JFu_PublicDigest35.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest35.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest35.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1408 32 (by decide)=NFY_JFu_PublicDigest35.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest35.window]
  exact NFY_JFu_PublicDigest35.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1408 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest35
-- END copied JFt_Digest35
-- BEGIN copied JFt_Digest36: lean/JFt_Digest36.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest36
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [260546973#u32,1375125357#u32,1584234519#u32,1097072342#u32,1685367984#u32,1070989054#u32,2113798037#u32,958210542#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest36.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest36.window
    NFY_JFu_PublicDigest36.length NFY_JFu_PublicDigest36.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest36.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest36.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1440 32 (by decide)=NFY_JFu_PublicDigest36.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest36.window]
  exact NFY_JFu_PublicDigest36.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1440 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest36
-- END copied JFt_Digest36

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
