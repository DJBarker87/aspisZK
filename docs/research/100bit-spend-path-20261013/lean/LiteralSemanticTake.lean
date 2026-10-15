import R1LiteralSemanticPrefix

/-! Successful strict semantic-prefix parsing is stable under taking the same
prefix of its input and output lists. This is list/Option plumbing only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticTake

open AspisR1.LiteralSemanticPrefix

theorem read_take
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (offset : Nat)
    (xs : List (LiteralSemanticPrefix.Message × LiteralSemanticPrefix.Challenge))
    (out : List (R0P.Mask.SemMsgZ LiteralSemanticPrefix.E × LiteralSemanticPrefix.E))
    (h : LiteralSemanticPrefix.read eK offset xs = some out) :
    ∀ n, LiteralSemanticPrefix.read eK offset (xs.take n) = some (out.take n) := by
  induction xs generalizing offset out with
  | nil =>
      intro n
      have hout : [] = out := by simpa [LiteralSemanticPrefix.read] using h
      subst out
      simp [LiteralSemanticPrefix.read]
  | cons item rest ih =>
      intro n
      cases n with
      | zero => simp [LiteralSemanticPrefix.read]
      | succ n =>
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
                        subst out
                        have hrest := ih (offset + 1) tail htail n
                        simp only [List.take_succ_cons, LiteralSemanticPrefix.read,
                          dif_pos hoff, hvalue, hmessage, Option.bind_eq_bind,
                          Option.bind_some, hrest, Option.map_some]
          · simp [LiteralSemanticPrefix.read, hoff] at h

#print axioms read_take

end AspisR1.LiteralSemanticTake
end
