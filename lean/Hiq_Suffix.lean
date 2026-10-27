import Hiq_ByteSelection
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_Suffix
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem drop_suffix (raw proof : Bytes) (long : 688 ≤ raw.length)
    (suffix : raw = raw.take 688 ++ proof) : raw.drop 688 = proof := by
  have h := congrArg (List.drop 688) suffix
  simpa only [List.drop_append,List.length_take,Nat.min_eq_left long,
    List.drop_take,Nat.sub_self,List.take_zero,List.nil_append,List.drop_zero] using h

theorem first (ops : AdapterRw.Ops) (a1 a2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops a1 a2 saved f s) :
    (Hiq_ByteSelection.account ops a1 0#usize).drop 688 = bytesOf f.proof.val ∧
      Hiq_ByteSelection.account ops a1 1#usize = bytesOf f.pub.val := by
  rw [Hiq_ByteSelection.account_read _ _ _ _ _ cuts.proof1Index cuts.proof1Read,
    Hiq_ByteSelection.account_read _ _ _ _ _ cuts.public1Index cuts.public1Read]
  refine ⟨drop_suffix _ _ ?_ cuts.firstSuffix,rfl⟩
  have len := congrArg List.length cuts.firstSuffix
  rw [List.length_append,List.length_take,cuts.proofLength] at len
  omega

theorem second (ops : AdapterRw.Ops) (a1 a2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops a1 a2 saved f s) :
    (Hiq_ByteSelection.account ops a2 0#usize).drop 688 = bytesOf s.proof.val := by
  rw [Hiq_ByteSelection.account_read _ _ _ _ _ cuts.proof2Index cuts.proof2Read]
  apply drop_suffix _ _ ?_ cuts.secondSuffix
  have ordered := S2X.successful_range_ordered s.raw s.proof 688#usize s.finish cuts.secondRange
  change 688 ≤ s.finish.val at ordered
  simpa only [bytesOf,List.length_map,cuts.raw2Length] using ordered

#print axioms drop_suffix
#print axioms first
#print axioms second
end AspisR1.Hiq_Suffix
end
