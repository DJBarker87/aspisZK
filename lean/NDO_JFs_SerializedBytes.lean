import NDO_JFs_SerializedDigests
import NDO_JFs_PublicSerialization
set_option autoImplicit false
namespace AspisR1.JFs_SerializedBytes
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431

def chunks : List (List U8) := [
  [0#u8],
  JFu_PublicDigest43.bytes,
  JFu_PublicDigest44.bytes,
  [77#u8,0#u8,0#u8,0#u8],
  [1#u8],
  JFu_PublicDigest45.bytes,
  JFu_PublicDigest46.bytes,
  [0#u8],
  [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8],
  JFu_PublicDigest02.bytes,
  JFu_PublicDigest03.bytes,
  JFu_PublicDigest04.bytes,
  JFu_PublicDigest05.bytes,
  JFu_PublicDigest06.bytes,
  JFu_PublicDigest07.bytes,
  JFu_PublicDigest08.bytes,
  JFu_PublicDigest09.bytes,
  JFu_PublicDigest10.bytes,
  JFu_PublicDigest11.bytes,
  JFu_PublicDigest12.bytes,
  JFu_PublicDigest13.bytes,
  JFu_PublicDigest14.bytes,
  JFu_PublicDigest15.bytes,
  JFu_PublicDigest16.bytes,
  JFu_PublicDigest17.bytes,
  JFu_PublicDigest18.bytes,
  JFu_PublicDigest19.bytes,
  JFu_PublicDigest20.bytes,
  JFu_PublicDigest21.bytes,
  JFu_PublicDigest22.bytes,
  JFu_PublicDigest23.bytes,
  JFu_PublicDigest24.bytes,
  JFu_PublicDigest25.bytes,
  JFu_PublicDigest26.bytes,
  JFu_PublicDigest27.bytes,
  JFu_PublicDigest28.bytes,
  JFu_PublicDigest29.bytes,
  JFu_PublicDigest30.bytes,
  JFu_PublicDigest31.bytes,
  JFu_PublicDigest32.bytes,
  JFu_PublicDigest33.bytes,
  JFu_PublicDigest34.bytes,
  JFu_PublicDigest35.bytes,
  JFu_PublicDigest36.bytes,
  JFu_PublicDigest37.bytes,
  JFu_PublicDigest38.bytes,
  JFu_PublicDigest39.bytes,
  JFu_PublicDigest40.bytes,
  JFu_PublicDigest41.bytes,
  JFu_PublicDigest42.bytes]
def bytes : List U8 := chunks.flatMap id

theorem source : (sourceSteps JFs_SerializerCanonical.value).flatMap stepBytes=bytes := by
  have asset : encodeWords [JFs_PaymentValue.common.asset_id]=[77#u8,0#u8,0#u8,0#u8] := by
    change encodeWords [core.num.U32.from_le_bytes JFs_Cell07.value]=_
    rw [JFs_PaymentValue.asset]
    simp [encodeWords,wordBytes,core.num.U32.to_le_bytes,BitVec.toLEBytes]
    <;> (repeat' constructor) <;> scalar_tac
  have index : (core.num.U64.to_le_bytes 13#u64).val=
      [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
    simp [core.num.U64.to_le_bytes,BitVec.toLEBytes]
    <;> (repeat' constructor) <;> scalar_tac
  have wordAppend (xs ys : List Field) : encodeWords (xs++ys)=encodeWords xs++encodeWords ys :=
    List.flatMap_append
  simp only [JFs_PaymentValue.common] at asset
  simp only [wordAppend,JFs_PaymentValue.common,JFs_SerializerCanonical.value,AspisR1TerminalDecoder.PublicBinding.toSerializer,
    JFs_PublicValue.value,AspisR1TerminalDecoder.PublicBinding.toTransfer,
    AspisR1TerminalDecoder.PublicBinding.toTransition,JFs_PublicValue.common,
    JFs_PaymentValue.value,JFs_LateChildren.value,sourceSteps,tailSteps,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,stepBytes,
    single,Array.to_slice,Array.make,rows,AspisR1PublicSerializer.Frontier431.row,
    JFt_SnapshotValue.value,JFt_AfterstateValue.value,
    List.getElem_cons_succ,List.getElem_cons_zero,asset,index,
    JFs_SerializedDigests.bytes00,
    JFs_SerializedDigests.bytes01,
    JFs_SerializedDigests.bytes02,
    JFs_SerializedDigests.bytes03,
    JFs_SerializedDigests.bytes04,
    JFs_SerializedDigests.bytes05,
    JFs_SerializedDigests.bytes06,
    JFs_SerializedDigests.bytes07,
    JFs_SerializedDigests.bytes08,
    JFs_SerializedDigests.bytes09,
    JFs_SerializedDigests.bytes10,
    JFs_SerializedDigests.bytes11,
    JFs_SerializedDigests.bytes12,
    JFs_SerializedDigests.bytes13,
    JFs_SerializedDigests.bytes14,
    JFs_SerializedDigests.bytes15,
    JFs_SerializedDigests.bytes16,
    JFs_SerializedDigests.bytes17,
    JFs_SerializedDigests.bytes18,
    JFs_SerializedDigests.bytes19,
    JFs_SerializedDigests.bytes20,
    JFs_SerializedDigests.bytes21,
    JFs_SerializedDigests.bytes22,
    JFs_SerializedDigests.bytes23,
    JFs_SerializedDigests.bytes24,
    JFs_SerializedDigests.bytes25,
    JFs_SerializedDigests.bytes26,
    JFs_SerializedDigests.bytes27,
    JFs_SerializedDigests.bytes28,
    JFs_SerializedDigests.bytes29,
    JFs_SerializedDigests.bytes30,
    JFs_SerializedDigests.bytes31,
    JFs_SerializedDigests.bytes32,
    JFs_SerializedDigests.bytes33,
    JFs_SerializedDigests.bytes34,
    JFs_SerializedDigests.bytes35,
    JFs_SerializedDigests.bytes36,
    JFs_SerializedDigests.bytes37,
    JFs_SerializedDigests.bytes38,
    JFs_SerializedDigests.bytes39,
    JFs_SerializedDigests.bytes40,
    JFs_SerializedDigests.bytes41,
    JFs_SerializedDigests.bytes42,
    JFs_SerializedDigests.bytes43,
    JFs_SerializedDigests.bytes44,
    JFs_SerializedDigests.bytes45,
    JFs_SerializedDigests.bytes46,
    bytes,chunks,List.nil_append,List.append_nil,List.append_assoc,id_eq]

#print axioms source
end AspisR1.JFs_SerializedBytes
