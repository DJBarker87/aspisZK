import R1SelectedTranscriptParams
import R1LiteralTranscript
import LiteralLegacyRun
import R1LiteralByteProtocol
import R1UnifiedProtocol

/-! Canonical front end for an already-decoded wire proof.  It chooses the
three protocol constructors by row and fills protocol-only word metadata with
zeros.  This is an adapter for the decoded input class; it does not establish
that the strict row parsers accept the decoded payloads. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CanonicalLiteralProof

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev BytesMessage := LiteralTranscript.BytesMessage
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Public := LiteralTranscript.Public
abbrev Proof := LiteralTranscript.Message
abbrev LiteralProof := LiteralProtocol.Proof
abbrev WireProof := State × (Nat → BytesMessage)

/-- The decoded input includes the parse witness needed to construct the
canonical tag-2 literal public statement, and the row-zero empty payload
convention needed for exact legacy-proof recovery. -/
structure DecodedInput where
  pubBytes : List SemanticPublicWire.Byte
  decodedPub : R0P.Public SemanticPublicWire.M31
  hparse : SemanticPublicWire.parsePublic pubBytes = some decodedPub
  wire : WireProof
  row0_empty : wire.2 0 = ⟨[], by simp [SelectedTranscriptParams.D]⟩

def publicOf (x : DecodedInput) : Public :=
  SelectedTranscriptParams.publicStatement x.pubBytes x.decodedPub x.hparse

def zeroC1 : LiteralTranscript.C1Word := fun _ => 0
def zeroC2 : LiteralTranscript.C2Word := fun _ _ => 0
def zeroV : LiteralTranscript.VWord := fun _ => 0

def literalMessage (wire : WireProof) (i : Nat) : Proof :=
  if h0 : i = 0 then .initial wire.1 zeroC1
  else if h2 : i = 2 then .c2 (wire.2 i) zeroC2
  else if h30 : i = 30 then .second (wire.2 i) zeroV
  else .payload (wire.2 i)

def literalProof (wire : WireProof) : LiteralProof := literalMessage wire

def outputOf (x : DecodedInput) : Public × LiteralProof :=
  (publicOf x, literalProof x.wire)

def liftProver (P : Program Bytes State DecodedInput) :
    Program Bytes State (Public × LiteralProof) :=
  bind P (fun x => Program.done (outputOf x))

theorem publicOf_tag2 (x : DecodedInput) : (publicOf x).tag = (2 : SemanticPublicWire.Byte) := by
  exact SelectedTranscriptParams.publicStatement_tag x.pubBytes x.decodedPub x.hparse

theorem literalProof_valid (wire : WireProof) (hzero : wire.2 0 = ⟨[], by simp [SelectedTranscriptParams.D]⟩) :
    ∀ i < 33, LiteralTranscript.valid i (literalProof wire i) := by
  intro i hi
  by_cases h0 : i = 0
  · subst i
    simp [literalProof, literalMessage, LiteralTranscript.valid]
  · by_cases h2 : i = 2
    · subst i
      simp [literalProof, literalMessage, LiteralTranscript.valid]
    · by_cases h30 : i = 30
      · subst i
        simp [literalProof, literalMessage, LiteralTranscript.valid]
      · simp [literalProof, literalMessage, LiteralTranscript.valid, h0, h2, h30, hi]

theorem literalProof_legacy_eq (wire : WireProof)
    (hzero : wire.2 0 = ⟨[], by simp [SelectedTranscriptParams.D]⟩) :
    LiteralLegacyRun.proof (literalProof wire) = wire := by
  apply Prod.ext
  · simp [LiteralLegacyRun.proof, LiteralLegacyRun.root, literalProof, literalMessage]
  · funext i
    by_cases h0 : i = 0
    · subst i
      simp [LiteralLegacyRun.proof, LiteralLegacyRun.bytesOf, literalProof, literalMessage, hzero]
    · by_cases h2 : i = 2
      · subst i
        simp [LiteralLegacyRun.proof, LiteralLegacyRun.bytesOf, literalProof, literalMessage]
      · by_cases h30 : i = 30
        · subst i
          simp [LiteralLegacyRun.proof, LiteralLegacyRun.bytesOf, literalProof, literalMessage]
        · simp [LiteralLegacyRun.proof, LiteralLegacyRun.bytesOf, literalProof, literalMessage, h0, h2, h30]

theorem literalMessage_erase_eq_wire (wire : WireProof)
    (hzero : wire.2 0 = ⟨[], by simp [SelectedTranscriptParams.D]⟩)
    (i : Nat) (hi : i < 33) :
    LiteralTranscript.erase (literalProof wire i) =
      LiteralLegacyRun.legacyProtocol.msg wire i := by
  have hlegacy := literalProof_legacy_eq wire hzero
  have hm := LiteralLegacyRun.message_eq (literalProof wire) (literalProof_valid wire hzero) i hi
  simpa [hlegacy] using hm

theorem erasedTranscript_eq_wire (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (wire : WireProof)
    (hzero : wire.2 0 = ⟨[], by simp [SelectedTranscriptParams.D]⟩)
    (n : Nat) (hn : n ≤ 33) :
    LiteralTranscript.erasePrefix
        ((LiteralByteProtocol.protocol decoder).transcript H pub (literalProof wire) n) =
      LiteralLegacyRun.legacyProtocol.transcript (fun a => H a.toBytes) pub wire n := by
  have h := LiteralLegacyRun.erased_transcript_eq decoder H pub (literalProof wire)
    (literalProof_valid wire hzero) n hn
  simpa [literalProof_legacy_eq wire hzero] using h

theorem literal_sampler_eq_wire (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : Public) (wire : WireProof)
    (hzero : wire.2 0 = ⟨[], by simp [SelectedTranscriptParams.D]⟩)
    (i : Nat) (hi : i < 33) :
    eval H ((LiteralByteProtocol.protocol decoder).chain H pub (literalProof wire) i).toProgram =
      mapView (fun a : LiteralProtocol.Address => a.toBytes)
        (eval (fun a => H a.toBytes)
          (LiteralLegacyRun.legacyProtocol.chain (fun a => H a.toBytes) pub wire i).toProgram) := by
  have h := LiteralLegacyRun.chain_eval_eq decoder H pub (literalProof wire)
    (literalProof_valid wire hzero) i hi
  rw [literalProof_legacy_eq wire hzero] at h
  exact h

theorem outputOf_valid (x : DecodedInput) :
    ∀ i < 33, LiteralTranscript.valid i ((outputOf x).2 i) :=
  literalProof_valid x.wire x.row0_empty

theorem eval_liftProver (P : Program Bytes State DecodedInput) (H : Bytes → State) :
    eval H (liftProver P) =
      let v := eval H P
      (v.1, outputOf v.2) := by
  rw [liftProver, eval_bind]
  simp [outputOf, eval]

theorem outputOf_public_tag2 (x : DecodedInput) : (outputOf x).1.tag = (2 : SemanticPublicWire.Byte) :=
  publicOf_tag2 x

#print axioms publicOf_tag2
#print axioms literalProof_valid
#print axioms literalProof_legacy_eq
#print axioms literalMessage_erase_eq_wire
#print axioms erasedTranscript_eq_wire
#print axioms literal_sampler_eq_wire
#print axioms outputOf_valid
#print axioms outputOf_public_tag2
#print axioms eval_liftProver

end AspisR1.CanonicalLiteralProof
end
