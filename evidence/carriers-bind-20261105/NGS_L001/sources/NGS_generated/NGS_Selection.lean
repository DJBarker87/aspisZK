import NGK_COMBINED_IMPORT
import ARU_SelectorPure
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGS_SELECTION
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open S2W_D189Wrappers GExq_AccountExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The checked native scanner range, ending at the raw buffer's end, is the
same complete suffix used by the charged selector. No equal-carrier premise. -/
theorem suffix (raw proof : Slice U8) (finish : Usize)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      raw {start := 688#usize, «end» := finish} = ok proof)
    (length : raw.val.length = finish.val) :
    (bytesOf raw.val).drop 688 = bytesOf proof.val := by
  have ordered := S2X.successful_range_ordered raw proof 688#usize finish range
  have shape := (AdapterRw.Ranges.suffix_exact raw proof 688#usize finish ordered length range).2
  change raw.val = raw.val.take 688 ++ proof.val at shape
  apply Hiq_Suffix.drop_suffix
  · simpa only [bytesOf,List.length_map,length] using ordered
  · simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape

/-- SAME physical getter/validator/encoder observations, not a selected-pair
output-equality hypothesis. The open enclosing drivers must supply them. -/
theorem on_packets {A : Type} (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (out : Outcome A) (reached : out.2.2.isSome = true)
    (f : FirstCut) (s : SecondCut) (finish1 : Usize)
    (proof1Index : Slice.index_usize out.1.entry.first 0#usize = ok f.proofAccount)
    (public1Index : Slice.index_usize out.1.entry.first 1#usize = ok f.publicAccount)
    (proof1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.proofAccount = ok (.Ok f.raw))
    (public1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.publicAccount = ok (.Ok f.pub))
    (range1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      f.raw {start := 688#usize, «end» := finish1} = ok f.proof)
    (length1 : f.raw.val.length = finish1.val)
    (proof2Index : Slice.index_usize ((out.2.2.get reached).1.entry.second secondSizes)
      0#usize = ok s.proofAccount)
    (proof2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.proofAccount = ok (.Ok s.raw))
    (range2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      s.raw {start := 688#usize, «end» := s.finish} = ok s.proof)
    (length2 : s.raw.val.length = s.finish.val)
    (v : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id
      ((out.2.2.get reached).1.entry.second secondSizes)
      (out.2.2.get reached).1.data (out.2.2.get reached).1.slot = ok (.Ok v))
    (encoding : ops.op22 v.statement = ok (.Ok s.encoded)) :
    Hiq_ByteSelection.select ops id out = Hist_PairExperiment.select ⟨f,s⟩ := by
  have p1 := Hiq_ByteSelection.account_read ops _ _ _ _ proof1Index proof1Read
  have u1 := Hiq_ByteSelection.account_read ops _ _ _ _ public1Index public1Read
  have p2 := Hiq_ByteSelection.account_read ops _ _ _ _ proof2Index proof2Read
  have u2 := Hiq_ByteSelection.public2_read ops id _ _ _ _ _ validation encoding
  have suffix1 := suffix f.raw f.proof finish1 range1 length1
  have suffix2 := suffix s.raw s.proof s.finish range2 length2
  unfold Hiq_ByteSelection.select
  cases h : out.2.2 with
  | none => simp only [h,Option.isSome_none,Bool.false_eq_true] at reached
  | some value =>
    simp only [h,Option.get_some] at p2 u2
    simp only [p1,u1,h,p2,u2,suffix1,suffix2,Hist_PairExperiment.select,
      SecondCut.pub,Array.to_slice]

/-- The charged selector's pure reads are unchanged by idealising only the
hash dictionary. This is a proved dictionary identity, not an experiment join. -/
theorem ideal_selector {A C : Type} (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (out : Outcome A) :
    Hiq_ByteSelection.select (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
      CPH_Program.verifier out = ARQ_Observer.select (FIp_Install.configuration err c r)
      CPH_Program.verifier out := by
  unfold ARQ_Observer.select Hiq_ByteSelection.select
  rw [ARU_SelectorPure.account,ARU_SelectorPure.public2,ARQ_Installation.dictionary]

#print axioms suffix
#print axioms on_packets
#print axioms ideal_selector
end AspisR1.NGS_SELECTION
end
