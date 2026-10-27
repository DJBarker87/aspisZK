import SCE_SubmissionExt
import SCE_FirstCutBytes
import ARQ_FirstOperandsBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_FirstBytes
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open SCE_Experiment MultiproofConeCanonical

/-- Associate the actual first trace's operands with the original submission.
Only source-prefix index/read/range observations are consumed. -/
theorem original {A : Type} (i : GExq_AccountExperiment.FirstInputs A) (ops : AdapterRw.Ops)
    (pa pu : AdapterRw.Cuts.Account) (raw pub proof : Slice U8)
    (index0 : Slice.index_usize i.entry.first 0#usize = ok pa)
    (index1 : Slice.index_usize i.entry.first 1#usize = ok pu)
    (rawRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pa = ok (.Ok raw))
    (pubRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pu = ok (.Ok pub))
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw {start := 688#usize,«end» := 58295#usize} = ok proof) :
    submitted i = (⟨bytesOf pub.val,bytesOf proof.val⟩ : F3T_ByteCarrier.Submission) := by
  have a0 := Result.ok.inj ((S2W_D189Entry.first_index i.entry).1.symm.trans index0)
  have a1 := Result.ok.inj ((S2W_D189Entry.first_index i.entry).2.1.symm.trans index1)
  rw [←a0] at rawRead
  rw [←a1] at pubRead
  have rawBytes := SCE_SnapshotRead.buffer i.entry ops 0 58295 58295 raw rawRead
  have publicBytes := SCE_SnapshotRead.buffer i.entry ops 1 1880 1880 pub pubRead
  have length : raw.val.length = 58295 := by
    rw [rawBytes.1]
    exact rawBytes.2.elim id id
  have shape := AdapterRw.Ranges.suffix_exact raw proof 688#usize 58295#usize
    (by scalar_tac) (by simpa using length) range
  have proofLength : (bytesOf proof.val).length = 57607 := by
    simpa only [bytesOf,List.length_map] using shape.1
  have suffix : bytesOf raw.val = (bytesOf raw.val).take 688 ++ bytesOf proof.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape.2
  apply SCE_SubmissionExt.equal
  · exact (congrArg bytesOf publicBytes.1).symm
  · change (bytesOf (i.entry.buffers (i.entry.handles 0).1).val).drop 688 = _
    rw [←rawBytes.1]
    exact SCE_SuffixShape.drop_eq _ _ suffix proofLength

#print axioms original
end AspisR1.ARQ_FirstBytes
end
