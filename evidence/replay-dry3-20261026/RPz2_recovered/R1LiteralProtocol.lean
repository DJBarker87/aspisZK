import R1LiteralRun
import R1GenericNoHitFS2
import R1SpendRelation

/-! Ideal word-message protocol carrier for the selected spend relation.
The decoder is an explicit parameter. Only its relation, transcript, and
D1 bookkeeping are established here; the concrete classifier, row density,
terminal acceptance, Merkle compilation, and efficient extraction remain open.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralProtocol

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open LiteralTranscript

abbrev Address := FS2.Duplex.Addr SelectedTranscriptParams.L
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Witness := SpendRelation.Wspend
abbrev Proof := Nat → LiteralTranscript.Message
abbrev Decoder := Address → Table Address State →
  Option (Sampler Address State (LiteralTranscript.Prefix × LiteralTranscript.Message × Challenge))

/-- The canonical public byte model and the checked spend relation. -/
def relation (pub : Public) (w : Witness) : Prop :=
  ∃ p, SemanticPublicWire.parsePublic pub.pubBytes = some p ∧ SpendRelation.Rspend p w

/-- The specification extractor selects a relation witness if one exists.
It is intentionally separate from the required executable Las Vegas extractor. -/
def protocol (decoder : Decoder) :
    FS2.Protocol Public LiteralTranscript.Message Challenge Witness Proof Address State where
  r := 33
  msg := fun pf i => pf i
  samp := LiteralTranscript.samp
  decode := decoder
  extract := fun pub _ => GenericNoHit.chooseWitness relation pub

theorem transcript_eq (decoder : Decoder) (H : Address → State) (pub : Public)
    (pf : Proof) (n : Nat) :
    (protocol decoder).transcript H pub pf n = LiteralRun.transcript H pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((protocol decoder).transcript H pub pf n).ext (pf n)
        (eval H (LiteralTranscript.samp n ((protocol decoder).transcript H pub pf n)
          (pf n)).toProgram).2 = _
      rw [ih]
      rfl

theorem erased_transcript (decoder : Decoder) (H : Address → State) (pub : Public)
    (pf : Proof) (n : Nat) :
    erasePrefix ((protocol decoder).transcript H pub pf n) =
      LiteralRun.erasedTranscript H pub pf n := by
  rw [transcript_eq]
  exact LiteralRun.erase_transcript H pub pf n

theorem d1 (decoder : Decoder)
    (bad : LiteralTranscript.Prefix → LiteralTranscript.Message → Challenge → Prop)
    (eps : Nat → ℚ) :
    FS2.D1 (protocol decoder) (GenericNoHitFS2.rows bad relation eps) :=
  GenericNoHitFS2.d1 (protocol decoder) bad relation eps (fun _ _ => rfl)

theorem extracted_relation (decoder : Decoder) (pub : Public)
    (T : Table Address State) (w : Witness)
    (h : (protocol decoder).extract pub T = some w) : relation pub w :=
  GenericNoHit.returned_relation relation pub w h

#print axioms transcript_eq
#print axioms erased_transcript
#print axioms d1
#print axioms extracted_relation

end AspisR1.LiteralProtocol
end
