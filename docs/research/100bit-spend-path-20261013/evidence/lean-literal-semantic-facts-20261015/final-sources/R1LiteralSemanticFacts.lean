import R1LiteralSemanticPrefix
import R1SelectedSemanticPrefixFacts

/-! List-level facts for the literal semantic-prefix reader. The reader
returns ordinary field challenges; query challenges are rejected. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticFacts

open R0P.Mask
open AspisR1.LiteralSemanticPrefix
open AspisR1.TranscriptView

theorem read_values (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (offset : Nat) (xs : List (LiteralSemanticPrefix.Message × LiteralSemanticPrefix.Challenge))
    (out : List (SemMsgZ LiteralSemanticPrefix.E × LiteralSemanticPrefix.E))
    (h : LiteralSemanticPrefix.read eK offset xs = some out) :
    out.map (fun p => Value.ordinary p.2) = xs.map (fun r => r.2.1) := by
  induction xs generalizing offset out with
  | nil =>
      simp [LiteralSemanticPrefix.read] at h
      subst out
      rfl
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hvalue : challenge.1 with
        | queries result => simp [LiteralSemanticPrefix.read, hoff, hvalue] at h
        | ordinary c =>
            cases hmessage : LiteralSemanticPrefix.parseMessage eK ⟨offset, hoff⟩ message with
            | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage] at h
            | some parsed =>
                cases htail : LiteralSemanticPrefix.read eK (offset + 1) rest with
                | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] at h
                | some tail =>
                    have hout : (parsed, c) :: tail = out := by
                      simpa [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] using h
                    cases hout
                    have hrest := ih (offset + 1) tail htail
                    simpa [hvalue] using
                      congrArg (List.cons (Value.ordinary c)) hrest
      · simp [LiteralSemanticPrefix.read, hoff] at h

theorem read_semChals (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (offset : Nat) (xs : List (LiteralSemanticPrefix.Message × LiteralSemanticPrefix.Challenge))
    (out : List (SemMsgZ LiteralSemanticPrefix.E × LiteralSemanticPrefix.E))
    (_h : LiteralSemanticPrefix.read eK offset xs = some out) :
    semChalsZ (SelectedSemanticPrefixFacts.lift out) = some (out.map Prod.snd) := by
  exact SelectedSemanticPrefixFacts.semChalsZ_lift out

#print axioms read_values
#print axioms read_semChals

end AspisR1.LiteralSemanticFacts
end
