import NLW_WriterHeader
import NLW_Persistence
import R9PoolRuntimeBinding
set_option autoImplicit false
noncomputable section
namespace NLW_AuthenticatedRoots
open Aeneas Aeneas.Std AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical
/-- Same saved/loaded checkpoint plus the SAME concrete header comparisons
 produce digestMatches; no digest injectivity is asserted. -/
theorem digest_matches (H : Bytes → State) (saved loaded proof1 pub1 proof2 pub2 : Slice U8)
 (persisted : bytesOf loaded.val=bytesOf saved.val)
 (writer : NLW_ReaderHeader.decode (bytesOf saved.val)=some (H (bytesOf proof1.val),H (bytesOf pub1.val)))
 (reader : NLW_ReaderHeader.decode (bytesOf loaded.val)=some (H (bytesOf proof2.val),H (bytesOf pub2.val))) :
 R9PoolRuntimeBinding.digestMatches H ⟨bytesOf proof1.val,bytesOf pub1.val⟩
  ⟨bytesOf proof2.val,bytesOf pub2.val⟩ := by
 rw [persisted,writer] at reader
 have eq:=Option.some.inj reader
 exact ⟨(congrArg Prod.fst eq).symm,(congrArg Prod.snd eq).symm⟩
/-- Both roots follow from OLD writer provenance, persistence, the reached
 resume header check, and the EXISTING pair-indexed P2-prime condition. This
 exposes rather than discharges collision binding; it is not an entry root. -/
theorem both (H : Bytes → State) (saved loaded proof1 pub1 proof2 pub2 : Slice U8)
 (p : OraclePortCompactDraft.Prepared)
 (a : QueryAccumulator.State OraclePortCompactDraft.K OraclePortCompactDraft.E)
 (encoding : bytesOf saved.val=OraclePortCheckpointAbiC5.encode H (bytesOf proof1.val) (bytesOf pub1.val) p a)
 (oldRoots : NLW_WriterPair.Roots p proof1)
 (persisted : bytesOf loaded.val=bytesOf saved.val)
 (reader : NLW_ReaderHeader.decode (bytesOf loaded.val)=some (H (bytesOf proof2.val),H (bytesOf pub2.val)))
 (binding : R9PoolRuntimeBinding.P2Prime H ⟨bytesOf proof1.val,bytesOf pub1.val⟩
  ⟨bytesOf proof2.val,bytesOf pub2.val⟩) :
 NLW_CommittedRoots.Both loaded proof2 := by
 have writer : NLW_ReaderHeader.decode (bytesOf saved.val)=
  some (H (bytesOf proof1.val),H (bytesOf pub1.val)) := by
  rw [encoding]; exact NLW_WriterHeader.decoded H _ _ p a
 have checked:=digest_matches H saved loaded proof1 pub1 proof2 pub2 persisted writer reader
 have equal:=binding checked
 exact NLW_ByteIdentity.both_transport saved loaded proof1 proof2
  (NLW_WriterPair.both H proof1 pub1 saved p a encoding oldRoots) persisted equal.1
#print digest_matches
#print both
#print axioms digest_matches
#print axioms both
end NLW_AuthenticatedRoots
