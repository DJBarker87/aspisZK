import R1LiteralSemanticPrefix
import R1TranscriptView

/-! A successful literal semantic-prefix parse records each indexed parsed
message, ordinary challenge, and in-range row index. This is structural parser
plumbing; message decoding remains opaque. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticIndex

open AspisR1.LiteralSemanticPrefix
open AspisR1.TranscriptView
open R0P.Mask

theorem read_index
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (offset : Nat)
    (xs : List (LiteralSemanticPrefix.Message × LiteralSemanticPrefix.Challenge))
    (out : List (SemMsgZ LiteralSemanticPrefix.E × LiteralSemanticPrefix.E))
    (hread : LiteralSemanticPrefix.read eK offset xs = some out) :
    ∀ (i : Nat) (hi : i < xs.length),
      ∃ hrow : offset + i < 25, ∃ parsed c,
        LiteralSemanticPrefix.parseMessage eK ⟨offset + i, hrow⟩ (xs[i]'hi).1 = some parsed ∧
        (xs[i]'hi).2.1 = Value.ordinary c ∧
        out[i]'(by rw [LiteralSemanticPrefix.read_length eK offset xs out hread]; exact hi) =
          (parsed, c) := by
  induction xs generalizing offset out with
  | nil =>
      intro i hi
      simp at hi
  | cons item rest ih =>
      intro i hi
      rcases item with ⟨message, challenge⟩
      cases i with
      | zero =>
          by_cases hoff : offset < 25
          · cases hvalue : challenge.1 with
            | queries result => simp [LiteralSemanticPrefix.read, hoff, hvalue] at hread
            | ordinary c =>
                cases hmessage : LiteralSemanticPrefix.parseMessage eK ⟨offset, hoff⟩ message with
                | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage] at hread
                | some parsed =>
                    cases htail : LiteralSemanticPrefix.read eK (offset + 1) rest with
                    | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] at hread
                    | some tail =>
                        have hout : (parsed, c) :: tail = out := by
                          simpa [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] using hread
                        subst out
                        refine ⟨hoff, parsed, c, ?_, ?_, ?_⟩
                        · simpa using hmessage
                        · simpa using hvalue
                        · simp
          · simp [LiteralSemanticPrefix.read, hoff] at hread
      | succ i =>
          by_cases hoff : offset < 25
          · cases hvalue : challenge.1 with
            | queries result => simp [LiteralSemanticPrefix.read, hoff, hvalue] at hread
            | ordinary c =>
                cases hmessage : LiteralSemanticPrefix.parseMessage eK ⟨offset, hoff⟩ message with
                | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage] at hread
                | some parsed =>
                    cases htail : LiteralSemanticPrefix.read eK (offset + 1) rest with
                    | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] at hread
                    | some tail =>
                        have hout : (parsed, c) :: tail = out := by
                          simpa [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] using hread
                        subst out
                        have hrest := ih (offset + 1) tail htail i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
                        obtain ⟨hrow', parsed', c', hparse', hchallenge', hindex'⟩ := hrest
                        have hrow : offset + (i + 1) < 25 := by omega
                        have hidx : offset + (i + 1) = (offset + 1) + i := by omega
                        refine ⟨hrow, parsed', c', ?_, ?_, ?_⟩
                        · simpa [hidx] using hparse'
                        · simpa using hchallenge'
                        · simpa using hindex'
          · simp [LiteralSemanticPrefix.read, hoff] at hread

#print axioms read_index

end AspisR1.LiteralSemanticIndex
end
