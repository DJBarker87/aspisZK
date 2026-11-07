import NMF_GameRoot
set_option autoImplicit false
noncomputable section
namespace NNC_SourceCuts
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical
open S2W_NativeConsolidation S2W_ExtractionBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Native read/range carrier without any TX2 op11 Result or model reader
Calls. TX1 facts remain on the writer side. Sibling 241/242 roots must produce
these fields at the selected occurrence; this is not an assumed native root. -/
structure Cuts (ops : AdapterRw.Ops) (accounts1 accounts2 : Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut) : Prop where
  proof1Index : Slice.index_usize accounts1 0#usize = ok f.proofAccount
  public1Index : Slice.index_usize accounts1 1#usize = ok f.publicAccount
  proof1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.proofAccount = ok (.Ok f.raw)
  public1Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.publicAccount = ok (.Ok f.pub)
  decode : ops.op47 f.pub = ok (.Ok f.statement)
  first : AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split = ok (.Ok saved)
  proofLength : (bytesOf f.proof.val).length = 57607
  firstSuffix : bytesOf f.raw.val = (bytesOf f.raw.val).take 688 ++ bytesOf f.proof.val
  proof2Index : Slice.index_usize accounts2 0#usize = ok s.proofAccount
  checkpoint2Index : Slice.index_usize accounts2 6#usize = ok s.checkpointAccount
  proof2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.proofAccount = ok (.Ok s.raw)
  checkpoint2Read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.checkpointAccount = ok (.Ok s.checkpoint)
  secondRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    s.raw {start := 688#usize, «end» := s.finish} = ok s.proof
  raw2Length : s.raw.val.length = s.finish.val
  secondSuffix : bytesOf s.raw.val = (bytesOf s.raw.val).take 688 ++ bytesOf s.proof.val


/-- Comparison with the older packet only; the native route never uses this
projection to manufacture a packet from model TX2 acceptance. -/
theorem of_source (ops : AdapterRw.Ops) (a1 a2 : Accounts)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (c : SourceCuts ops a1 a2 saved f s) : Cuts ops a1 a2 saved f s :=
 ⟨c.proof1Index,c.public1Index,c.proof1Read,c.public1Read,c.decode,c.first,
 c.proofLength,c.firstSuffix,c.proof2Index,c.checkpoint2Index,c.proof2Read,
 c.checkpoint2Read,c.secondRange,c.raw2Length,c.secondSuffix⟩
theorem first (ops : AdapterRw.Ops) (a1 a2 : Accounts)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (cuts : Cuts ops a1 a2 saved f s) :
 (Hiq_ByteSelection.account ops a1 0#usize).drop 688=bytesOf f.proof.val ∧
 Hiq_ByteSelection.account ops a1 1#usize=bytesOf f.pub.val := by
 rw [Hiq_ByteSelection.account_read _ _ _ _ _ cuts.proof1Index cuts.proof1Read,
  Hiq_ByteSelection.account_read _ _ _ _ _ cuts.public1Index cuts.public1Read]
 refine ⟨Hiq_Suffix.drop_suffix _ _ ?_ cuts.firstSuffix,rfl⟩
 have len:=congrArg List.length cuts.firstSuffix
 rw [List.length_append,List.length_take,cuts.proofLength] at len
 omega
theorem second (ops : AdapterRw.Ops) (a1 a2 : Accounts)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (cuts : Cuts ops a1 a2 saved f s) :
 (Hiq_ByteSelection.account ops a2 0#usize).drop 688=bytesOf s.proof.val := by
 rw [Hiq_ByteSelection.account_read _ _ _ _ _ cuts.proof2Index cuts.proof2Read]
 apply Hiq_Suffix.drop_suffix _ _ ?_ cuts.secondSuffix
 have ordered:=S2X.successful_range_ordered s.raw s.proof 688#usize s.finish cuts.secondRange
 change 688≤s.finish.val at ordered
 simpa only [bytesOf,List.length_map,cuts.raw2Length] using ordered
/-- P2P selection needs account reads/ranges and validation/encoding only;
its former SourceCuts.second field is entirely absent. -/
theorem on_cuts (ops : AdapterRw.Ops) (id : Program)
 (e1 e2 : S2W_D189Entry.Entry) (data2 : Slice U8) (slot : Slot)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (cuts : Cuts ops e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s)
 (origin : P2P_Origin.Fact ops id (e2.second S2W_D189Wrappers.secondSizes) data2 slot s) :
 P2P_NativeSelection.pair ops id e1 e2 data2 slot=Hist_PairExperiment.select ⟨f,s⟩ := by
 obtain ⟨v,validate,encode⟩:=origin
 obtain ⟨proof1,public1⟩:=first _ _ _ _ _ _ cuts
 have proof2:=second _ _ _ _ _ _ cuts
 have public2:=Hiq_ByteSelection.public2_read _ _ _ _ _ _ _ validate encode
 simp only [P2P_NativeSelection.pair,Hist_PairExperiment.select,proof1,public1,proof2,public2]
 rfl
#print Cuts
#print on_cuts
#print axioms of_source
#print axioms first
#print axioms second
#print axioms on_cuts
end NNC_SourceCuts
