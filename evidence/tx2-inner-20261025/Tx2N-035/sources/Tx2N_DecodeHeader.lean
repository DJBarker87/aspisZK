import Tx2N_Reserved
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_DecodeHeader
open Aeneas Aeneas.Std Result AspisR1Stage2
open MultiproofConeCanonical OraclePortCompactDraft

theorem range_to (ck out : Slice U8) (n : Usize) (bound : n.val ≤ ck.val.length)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      ck {«end»:=n} = ok out) : out.val = ck.val.take n.val := by
  obtain ⟨s,call,contents,len⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec {«end»:=n} ck bound)
  have same := Result.ok.inj (call.symm.trans read)
  subst out
  simpa only [List.slice,List.extract_eq_drop_take,Nat.sub_zero,List.drop_zero] using contents

theorem byte (ck : Slice U8) (i : Usize) (b : U8) (bound : i.val < ck.val.length)
    (read : Slice.index_usize ck i = ok b) : ck.val[i.val] = b := by
  simpa [Slice.index_usize,bound] using read

theorem cast_value (x : U8) : (UScalar.cast .Usize x).val = x.val := by
  change (x.bv.setWidth System.Platform.numBits).toNat = x.val
  rw [BitVec.toNat_setWidth_of_le (by rcases System.Platform.numBits_eq with h|h <;> omega)]
  rfl

theorem accepted (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (ck proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (next : a.next = 10#usize)
    (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D ck proof pub .S2 hash = ok (.Ok (p,a))) :
    slice (bytesOf ck.val) 0 16 = OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0] := by
  obtain ⟨magic,reservedBytes,nextByte,iterator,rest,length,magicRead,magicEq,tagRead,nextRead,
    versionRead,reservedRead,iterRead,scan⟩ := Tx2N_Header.cuts reserved D ck proof pub hash p a success
  have eight : (8#usize : Usize).val = 8 := by scalar_tac
  have nine : (9#usize : Usize).val = 9 := by scalar_tac
  have ten : (10#usize : Usize).val = 10 := by scalar_tac
  have front := range_to ck magic 8#usize (by rw [eight,length]; decide) magicRead
  have suffixRun := MultiproofConeSlices.range_total ck 11#usize 16#usize (by decide) (by change 16 ≤ ck.val.length; omega)
  have suffixEq := Result.ok.inj (reservedRead.symm.trans suffixRun)
  have suffix : reservedBytes.val = (ck.val.drop 11).take 5 := by
    rw [suffixEq]
    rfl
  have reservedSize : reservedBytes.val.length = 5 := by rw [suffix]; simp [length]
  have iter : iterator = ⟨reservedBytes,0⟩ := Result.ok.inj iterRead.symm
  rw [iter] at scan
  have zero := Tx2N_Reserved.zeros reservedBytes rest reservedSize scan
  obtain ⟨fields⟩ := CheckpointBytes4Ops.successful_fields reserved D ck proof pub .S2 hash p a success
  have sameByte : fields.nextByte = nextByte := Result.ok.inj (fields.nextRead.symm.trans nextRead)
  have cast : UScalar.cast .Usize nextByte = a.next := by
    rw [← sameByte]
    exact Result.ok.inj fields.nextCast
  have nextVal : nextByte.val = 10 := by
    rw [← cast_value,cast,next]
    rfl
  have nextEq : nextByte = 10#u8 := UScalar.eq_of_val_eq nextVal
  rw [nextEq] at nextRead
  have t8 := byte ck 8#usize 2#u8 (by rw [eight,length]; decide) tagRead
  have t9 := byte ck 9#usize 10#u8 (by rw [nine,length]; decide) nextRead
  have t10 := byte ck 10#usize 1#u8 (by rw [ten,length]; decide) versionRead
  rw [eight] at front
  simp only [eight] at t8
  simp only [nine] at t9
  simp only [ten] at t10
  have one8 : (ck.val.drop 8).take 1 = [2#u8] := by
    simp only [List.take_one,List.head?_drop,List.getElem?_eq_getElem (show 8 < ck.val.length by omega),t8]
    rfl
  have one9 : (ck.val.drop 9).take 1 = [10#u8] := by
    simp only [List.take_one,List.head?_drop,List.getElem?_eq_getElem (show 9 < ck.val.length by omega),t9]
    rfl
  have one10 : (ck.val.drop 10).take 1 = [1#u8] := by
    simp only [List.take_one,List.head?_drop,List.getElem?_eq_getElem (show 10 < ck.val.length by omega),t10]
    rfl
  have full : ck.val.take 16 = magic.val ++ [2#u8,10#u8,1#u8] ++ List.replicate 5 0#u8 := by
    rw [show 16=8+(1+(1+(1+5))) by decide,List.take_add,List.take_add,List.drop_drop,
      List.take_add,List.drop_drop,List.take_add,List.drop_drop]
    change ck.val.take 8 ++ ((ck.val.drop 8).take 1 ++
      ((ck.val.drop 9).take 1 ++ ((ck.val.drop 10).take 1 ++ (ck.val.drop 11).take 5))) = _
    rw [← front,one8,one9,one10,← suffix,zero]
    simp only [List.singleton_append,List.append_assoc]
  have mapped : bytesOf (ck.val.take 16) = OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0] := by
    rw [full,magicEq]
    rfl
  simpa only [slice,List.drop_zero,bytesOf,List.map_take] using mapped

#print axioms range_to
#print axioms byte
#print axioms cast_value
#print axioms accepted
end AspisR1.Tx2N_DecodeHeader
end
