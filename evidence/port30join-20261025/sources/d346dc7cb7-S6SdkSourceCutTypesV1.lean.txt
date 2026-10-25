import S6SdkDependencyFactorV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.AdapterRw.LeadInputs
abbrev Public := AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

end AspisR1.AdapterRw.LeadInputs

namespace AspisR1.S2W_NativeConsolidation
open S2W_ExtractionBoundary MultiproofConeCanonical
structure FirstCut where
  proofAccount : AdapterRw.Cuts.Account
  publicAccount : AdapterRw.Cuts.Account
  raw : Slice U8
  pub : Slice U8
  statement : AdapterRw.Cuts.Statement
  semantic : AdapterRw.LeadInputs.Public
  proof : Slice U8
  split : Usize

structure SecondCut where
  proofAccount : AdapterRw.Cuts.Account
  checkpointAccount : AdapterRw.Cuts.Account
  raw : Slice U8
  checkpoint : Slice U8
  encoded : Array U8 1880#usize
  proof : Slice U8
  finish : Usize

def SecondCut.pub (s : SecondCut) : Slice U8 := Array.to_slice s.encoded

/-- Only exact source read/dispatch/checked-range facts; all obtained from
accepted source execution by cuts_of_acceptance below. Not trusted. -/
structure SourceCuts (ops : AdapterRw.Ops) (accounts1 accounts2 : Accounts)
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
  second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    s.pub s.proof s.checkpoint () none = ok (.Ok ())
  secondSuffix : bytesOf s.raw.val = (bytesOf s.raw.val).take 688 ++ bytesOf s.proof.val

end AspisR1.S2W_NativeConsolidation
