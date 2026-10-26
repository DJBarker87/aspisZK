import S2W_AuthenticatedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_Authentication
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_AuthenticatedInputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Persistence authenticates TX1's two digest values. No injectivity or
identity of the attacker-chosen TX2 buffers follows from this theorem. -/
theorem digest_matches (ops : AdapterRw.Ops) (decode : HeaderDecode)
    (H : Bytes → State) (semantic : Public) (pub1 proof1 pub2 proof2 loaded : Slice U8)
    (split : Usize) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded ops semantic pub1 proof1 split = ok (.Ok saved))
    (second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub2 proof2 loaded () none = ok (.Ok ()))
    (writer : CheckpointWriterConeJoin ops decode H semantic pub1 proof1 split)
    (reader : CheckpointReaderConeJoin ops decode H pub2 proof2 loaded)
    (version : CheckpointVersionBinding (bytesOf saved.val) (bytesOf loaded.val)) :
    R9PoolRuntimeBinding.digestMatches H
      ⟨bytesOf proof1.val,bytesOf pub1.val⟩ ⟨bytesOf proof2.val,bytesOf pub2.val⟩ := by
  have persisted := S2X.checkpoint_persistence _ _ version.history
  have wrote := writer.header saved first
  have read := reader.checkedHeader second
  rw [persisted,wrote] at read
  have pairs := Option.some.inj read
  exact ⟨(congrArg Prod.fst pairs).symm,(congrArg Prod.snd pairs).symm⟩

#print axioms digest_matches
end AspisR1.P2P_Authentication
end
