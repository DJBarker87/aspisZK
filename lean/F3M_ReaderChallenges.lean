import F3L_InputOpening
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ReaderChallenges
open LiteralTranscript

def ordinaryValues (rs : List (Message × Challenge)) : List LiteralTranscript.E :=
  rs.map (fun mc => match mc.2.1 with | .ordinary x => x | .queries _ => 0)

theorem values (offset : Nat) (rs : List (Message × Challenge))
    (out : List (R0P.Mask.SemMsgZ LiteralTranscript.E × LiteralTranscript.E))
    (read : LiteralSemanticPrefix.read LiteralOpeningView.eK offset rs=some out) :
    out.map Prod.snd=ordinaryValues rs := by
  induction rs generalizing offset out with
  | nil => simp only [LiteralSemanticPrefix.read,Option.some.injEq] at read; subst out; rfl
  | cons mc rest ih =>
    rcases mc with ⟨m,c⟩
    unfold LiteralSemanticPrefix.read at read
    split at read
    · rename_i below
      cases ch : c.1 with
      | queries q => simp only [ch] at read; contradiction
      | ordinary x =>
        simp only [ch] at read
        cases parsed : LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK ⟨offset,below⟩ m with
        | none => simp only [parsed,Option.bind_none] at read; contradiction
        | some msg =>
          cases tail : LiteralSemanticPrefix.read LiteralOpeningView.eK (offset+1) rest with
          | none => simp only [parsed,Option.bind_some,tail,Option.map_none] at read; contradiction
          | some xs =>
            simp only [parsed,Option.bind_some,tail,Option.map_some,Option.some.injEq] at read
            subst out
            simp only [List.map_cons,Prod.snd,ih _ _ tail,ordinaryValues,ch]
    · contradiction

#print axioms values
end AspisR1.F3M_ReaderChallenges
end
