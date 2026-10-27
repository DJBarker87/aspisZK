import F3T_RootAgreement
import F3T_Reached
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AlignedRows
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

theorem lookup (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (row : Nat) (below : row<33) :
    ∃ c,(LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf 33)).rounds[row]?=
      some (LiteralTranscript.erase (pf row),c) := by
  refine ⟨(eval H (LiteralByteSampler.samp row
    ((LiteralByteProtocol.protocol D).transcript H pub pf row) (pf row)).toProgram).2,?_⟩
  simp only [LiteralTranscript.erasePrefix,List.getElem?_map,
    LiteralByteRunFacts.transcript_index D H pub pf 33 row below,Option.map_some]

theorem initial (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (p : Parsed)
    (aligned : Aligned p (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33))) :
    ∃ root,LiteralTranscript.erase (pf 0)=.initial root ∧ bytes root=root0 p := by
  obtain ⟨root,c,atRoot,rootBytes⟩ := aligned.2.2.2.1
  obtain ⟨challenge,atProof⟩ := lookup D H pub pf 0 (by decide)
  have same := congrArg Prod.fst (Option.some.inj (atProof.symm.trans atRoot))
  exact ⟨root,same,rootBytes⟩

theorem payload (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (p : Parsed)
    (aligned : Aligned p (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33)))
    (row : Nat) (positive : 0<row) (below : row<33) :
    ∃ b,LiteralTranscript.erase (pf row)=.payload b ∧ b.val=rowBytes p row := by
  obtain ⟨b,c,atPayload,payloadBytes⟩ := aligned.2.2.2.2 row positive below
  obtain ⟨challenge,atProof⟩ := lookup D H pub pf row below
  exact ⟨b,congrArg Prod.fst (Option.some.inj (atProof.symm.trans atPayload)),payloadBytes⟩

theorem canonical_rows (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) (p : Parsed)
    (aligned : Aligned p (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33)))
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (row : Nat) (below : row<33) :
    LiteralTranscript.erase (pf row)=LiteralTranscript.erase (Port1_StoredCarrier.parsedProof p row) := by
  by_cases zero : row=0
  · subst row
    obtain ⟨root,initial,rootBytes⟩ := initial D H pub pf p aligned
    rw [initial,F3T_RootAgreement.from_bytes p root rootBytes]
    rfl
  · obtain ⟨b,atPayload,payloadBytes⟩ := payload D H pub pf p aligned row (by omega) below
    have bytesEq : b=Port1_StoredCarrier.payload (rowBytes p row) := by
      rw [F3T_ProofCarriers.payload_eq p bound row]
      exact Subtype.ext payloadBytes
    rw [atPayload,bytesEq]
    unfold Port1_StoredCarrier.parsedProof
    split_ifs <;> first | contradiction | rfl

#print axioms canonical_rows
#print axioms payload
#print axioms lookup
#print axioms initial
end AspisR1.F3T_AlignedRows
end
