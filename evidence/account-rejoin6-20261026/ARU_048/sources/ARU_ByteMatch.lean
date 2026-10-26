import ARU_FirstHeader
import ARU_SecondHeader
import P2P_Origin
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_ByteMatch
open Aeneas Aeneas.Std Result S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem digest_matches {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SCH_IdealSdk.dictionary c hashv H) accounts1 accounts2 saved f s)
    (checkpoint : bytesOf s.checkpoint.val = bytesOf saved.val) :
    R9PoolRuntimeBinding.digestMatches H ⟨bytesOf f.proof.val,bytesOf f.pub.val⟩
      ⟨bytesOf s.proof.val,bytesOf s.pub.val⟩ := by
  have wrote := ARU_FirstHeader.accepted c hashv H f.semantic f.pub f.proof f.split saved cuts.first
  have read := ARU_SecondHeader.accepted c hashv H s.pub s.proof s.checkpoint cuts.second
  rw [checkpoint] at read
  have pairs := Option.some.inj (wrote.1.symm.trans read)
  exact ⟨congrArg Prod.fst pairs,congrArg Prod.snd pairs⟩

#print axioms digest_matches
end AspisR1.ARU_ByteMatch
end
