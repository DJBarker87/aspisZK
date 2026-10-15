import R1LiteralClassifier
import R1LiteralProtocol

/-! D1 and D2 for the concrete literal-word classifier over unrestricted byte
oracle inputs. The decoder remains an explicit parameter. This does not supply
D3, a decoder injection theorem, a Merkle compiler, source refinement, or the
required efficient extractor; the extractor here is specification-level choice. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralByteProtocol

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.DuplexFrames
open LiteralTranscript

abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Decoder := Bytes → Table Bytes State →
  Option (Sampler Bytes State (LiteralTranscript.Prefix × LiteralTranscript.Message × Challenge))

def protocol (decoder : Decoder) :
    FS2.Protocol Public LiteralTranscript.Message Challenge LiteralProtocol.Witness
      LiteralProtocol.Proof Bytes State where
  r := 33
  msg := fun pf i => pf i
  samp := LiteralByteSampler.samp
  decode := decoder
  extract := fun pub _ => GenericNoHit.chooseWitness LiteralProtocol.relation pub

def rows : RoundByRound' Public LiteralTranscript.Message Challenge Bytes State :=
  GenericNoHitFS2.rows LiteralClassifier.bad LiteralProtocol.relation LiteralClassifier.budget

theorem d1 (decoder : Decoder) : D1 (protocol decoder) rows :=
  GenericNoHitFS2.d1 (protocol decoder) LiteralClassifier.bad LiteralProtocol.relation
    LiteralClassifier.budget (fun _ _ => rfl)

theorem d2 (decoder : Decoder) : D2 (protocol decoder) rows := by
  apply GenericNoHitFS2.d2 (protocol decoder) LiteralClassifier.bad
    LiteralProtocol.relation LiteralClassifier.budget
  intro i P m hround hi _
  subst i
  exact LiteralClassifier.byte_density P m hi

#print axioms d1
#print axioms d2

end AspisR1.LiteralByteProtocol
end
