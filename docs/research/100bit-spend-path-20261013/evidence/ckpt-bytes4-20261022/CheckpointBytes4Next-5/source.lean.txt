import CheckpointBytes4Ops
import CheckpointBytesDigest

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4Next
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Ops
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCheckpointSlicesC5

/-- The actual next-byte read and cast recover the saved-ten cursor. -/
theorem next_value (reserved : Bool) (ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (f : OraclePortCkptAbiSourceFields.Fields (ops reserved) ck .S2 p a)
    (H : Bytes → State) (stored pub : Bytes) (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K E)
    (encoding : bytesOf ck.val = encode H stored pub pm am) : a.next.val = 10 := by
  have length : ck.val.length = 1768 := by
    have h := congrArg List.length encoding
    simpa only [bytesOf,List.length_map,encode_length] using h
  have bound : 9 < ck.val.length := by omega
  have sourceRead := f.nextRead
  simp [Slice.index_usize,bound] at sourceRead
  have byteEq : ck.val[9]'bound = f.nextByte := sourceRead
  have header := (prefix_slices H stored pub pm am).1
  rw [← encoding] at header
  have ninth := congrArg (fun b : Bytes => b[9]?) header
  have ninth' : (bytesOf ck.val)[9]? = some (10 : Fin 256) := by
    simpa [slice,OraclePortPhysicalFrameDraft.magic] using ninth
  have mapRead : (bytesOf ck.val)[9]? =
      some (AspisV8R19.SqueezeOracleBridge.decodeByte (ck.val[9]'bound)) := by
    simp only [bytesOf,List.getElem?_map,List.getElem?_eq_getElem bound,Option.map_some]
  rw [mapRead] at ninth'
  have byteVal := congrArg Fin.val (Option.some.inj ninth')
  change (ck.val[9]'bound).val = 10 at byteVal
  rw [byteEq] at byteVal
  have castEq : UScalar.cast .Usize f.nextByte = a.next := Result.ok.inj f.nextCast
  rw [← castEq]
  simp only [UScalar.cast]
  change (f.nextByte.bv.setWidth System.Platform.numBits).toNat = 10
  rw [BitVec.toNat_setWidth_of_le (by
    rcases System.Platform.numBits_eq with h | h <;> omega)]
  exact byteVal

#print axioms next_value
end AspisR1.CheckpointBytes4Next
end
