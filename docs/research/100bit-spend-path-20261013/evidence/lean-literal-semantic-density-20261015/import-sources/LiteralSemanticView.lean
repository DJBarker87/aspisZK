import R1LiteralSemanticPrefix
import R1SelectedSemanticPrefixFacts
import R1LiteralTypedContext
import R1PublicBaseMap
import R1ExactBaseProjection
import R0P.MaskD2Glue
import R0P.MaskValue

/-! Causal, table-free semantic views of literal-message prefixes. C1 is read
from row zero (the current message at round zero); C2 is read only from the
message carrying it. The old semantic density theorem is reused on this
view. This does not establish the later terminal or compiler implication. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticView

open FS R0P R0P.SemSource R0P.Mask
open AspisV8R15.ExactTowerBase AspisWideTower
open AspisV8R19.SourceDuplexStep AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

abbrev E := WideExact
def eK : QM31Exact →+* E := algebraMap QM31Exact E
abbrev F := ExactBaseProjection.embed.fieldRange
abbrev S := LiteralTypedWords.laneSubfield ExactBaseProjection.embed eK
abbrev Context := TypedContext E S

structure View (round : Nat) where
  context : Context
  rounds : List (SemMsgZ E × E)
  length_eq : rounds.length = round
  message : SemMsgZ E

def View.prefix {round : Nat} (v : View round) : FS.Prefix Context (MsgZ E) (ChalZ E) :=
  ⟨v.context, SelectedSemanticPrefixFacts.lift v.rounds⟩

theorem View.prefix_length {round : Nat} (v : View round) :
    v.prefix.rounds.length = round := by
  simpa [View.prefix, SelectedSemanticPrefixFacts.lift] using v.length_eq

/-- The appended marker supplies only the current message. Its dummy challenge
is never consumed by the semantic-prefix reader. -/
def read (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Option (View P.round) :=
  if hrow : P.round < 25 then do
    let pub ← SemanticPublicWire.parsePublic P.statement.pubBytes
    let c1 ← LiteralTranscript.c1At
      (P.rounds ++ [(m, (TranscriptView.Value.ordinary 0, 0))])
    match hread : LiteralSemanticPrefix.read eK 0 P.rounds with
    | none => none
    | some rounds => do
        let current ← LiteralSemanticPrefix.parseMessage eK ⟨P.round, hrow⟩ m
        pure ⟨LiteralTypedContext.context ExactBaseProjection.embed eK
          (SpendDataMap.mapPublic ExactBaseProjection.embed pub)
          (PublicBaseMap.mapPublic_base ExactBaseProjection.embed pub) c1 (fun _ => 0),
          rounds, LiteralSemanticPrefix.read_length eK 0 P.rounds rounds hread, current⟩
  else none

/-- Only a successfully parsed, fixed semantic view contributes a bad event. -/
def bad (B : PackBasis F) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (c : E) : Prop :=
  match read P m with
  | none => False
  | some v => semanticBadZ (maskClaimsR0 B) B v.prefix v.message c

theorem density (B : PackBasis F) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (hi : P.round < 25) :
    mean (fun s : State => indicator (bad B P m (semChal s))) ≤
      combinedD2BudgetZ P.round := by
  classical
  cases h : read P m with
  | none =>
      simp only [bad, h, indicator_false, mean_const]
      exact combinedD2BudgetZ_nonneg P.round
  | some v =>
      have hlen := v.prefix_length
      have hd := semantic_round_densityZ (maskClaimsR0 B) B v.prefix v.message
        (by rw [hlen]; exact hi)
      simpa only [bad, h, hlen] using hd

#print axioms View.prefix_length
#print axioms density

end AspisR1.LiteralSemanticView
end
