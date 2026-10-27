import RPz7_Tx2N_Reader
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Header
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Ops

theorem guard {T : Type} (b : Bool) (tail : Result (core.result.Result T verifier.Error))
    (out : T) (h : (if b then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    b = false ∧ tail = ok (.Ok out) := by
  cases b
  · exact ⟨rfl,h⟩
  · cases h

theorem guard_prop {T : Type} (b : Prop) [Decidable b]
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    ¬b ∧ tail = ok (.Ok out) := by
  by_cases hb : b
  · rw [if_pos hb] at h
    cases h
  · exact ⟨hb,by rwa [if_neg hb] at h⟩

/-- The concrete reader's header cuts, including the reserved-byte scan.
All are from this successful resume, with no encoding premise. -/
theorem cuts (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (ck proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (ops reserved) D ck proof pub .S2 hash = ok (.Ok (p,a))) :
    ∃ (magic reservedBytes : Slice U8) (next : U8) (iterator rest : core.slice.iter.Iter U8),
      ck.val.length = 1768 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        ck {«end» := 8#usize} = ok magic ∧
      magic.val = [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8] ∧
      Slice.index_usize ck 8#usize = ok 2#u8 ∧
      Slice.index_usize ck 9#usize = ok next ∧
      Slice.index_usize ck 10#usize = ok 1#u8 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        ck {start := 11#usize,«end» := 16#usize} = ok reservedBytes ∧
      core.slice.Slice.iter reservedBytes = ok iterator ∧
      headerAny iterator = ok (false,rest) := by
  unfold verifier.resumeWithOps at success
  obtain ⟨size,sizeCall,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
  have sizeEq : size = 1768#usize := by
    have known : (ops reserved).checkpointSize .S2 = ok 1768#usize := by
      simp only [ops,checkpointSize,finalLen,bind_tc_ok]
      rw [Port4A_ReaderInstall.mul_value _ _ (by decide),bind_tc_ok,
        Port4A_ReaderInstall.add_value _ _ (by decide)]
      congr 1
    exact Result.ok.inj (sizeCall.symm.trans known)
  subst size
  obtain ⟨lengthGuard,h⟩ := guard _ _ _ h
  have length : ck.val.length = 1768 := by
    have same : Slice.len ck = 1768#usize := by simpa only [bne_iff_ne,ne_eq,not_not] using (Bool.eq_false_iff.mp lengthGuard)
    exact congrArg UScalar.val same
  obtain ⟨magic,magicRead,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨bad,compare,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨rfl,h⟩ := guard bad _ _ h
  have magicEq := CheckpointBytes4Comparison.ne_sound magic
    (Array.make 8#usize [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8]) compare
  obtain ⟨tag,tagRead,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨tag1,tagCall,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  have tagEq : tag1 = 2#u8 := Result.ok.inj tagCall.symm
  subst tag1
  obtain ⟨tagGuard,h⟩ := guard _ _ _ h
  have tagEq : tag = 2#u8 := by simpa only [bne_iff_ne,ne_eq,not_not] using (Bool.eq_false_iff.mp tagGuard)
  subst tag
  obtain ⟨next,nextRead,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨_,h⟩ := guard_prop (next > 22#u8) _ _ h
  obtain ⟨version,versionRead,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨versionGuard,h⟩ := guard _ _ _ h
  have versionEq : version = 1#u8 := by simpa only [bne_iff_ne,ne_eq,not_not] using (Bool.eq_false_iff.mp versionGuard)
  subst version
  obtain ⟨reservedBytes,reservedRead,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨iterator,iterRead,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨⟨bad,rest⟩,scan,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨rfl,h⟩ := guard bad _ _ h
  exact ⟨magic,reservedBytes,next,iterator,rest,length,magicRead,magicEq,tagRead,nextRead,
    versionRead,reservedRead,iterRead,scan⟩

#print axioms guard
#print axioms guard_prop
#print axioms cuts
end AspisR1.Tx2N_Header
end
