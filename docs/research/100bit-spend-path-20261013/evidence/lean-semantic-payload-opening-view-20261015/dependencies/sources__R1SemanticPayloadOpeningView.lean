import R1SemanticPayloadView
import R0P.MaskView

/-! Package the typed 25-row payload view with the existing R0 circle/opening
view parser. This is model-view plumbing only; it asserts no protocol
acceptance or source correspondence. -/
set_option autoImplicit false

namespace AspisR1.SemanticPayloadOpeningView

open R0C.SemStatement
open R0P.Mask
open R0P.SemSource
open AspisR1.SemanticPayloadView
open AspisR1.SemanticRecordCodec
open AspisPool.AlgorithmicCircleDecoderV7

abbrev E := AspisWideTower.WideExact

variable {Sfield : Fin 29 → Subfield E}

/-- The row-indexed payload constructors and explicit C2 callback produce
exactly the prefix consumed by the old opening-view parser. Circle
non-rationality and C2-base conditions remain explicit parser premises. -/
theorem opening_view_of_payloads
    (x : TypedContext E Sfield)
    (recoverC2 : State → InitialWord E × InitialWord E)
    (payloads : (row : Fin 25) → RowPayload row)
    (challenges : Fin 25 → E)
    (hb : R0P.SemSource.c2Base Sfield
      (recoverC2 (rootAt2 payloads)).1 (recoverC2 (rootAt2 payloads)).2)
    (y : Fin 3 → Fin 29 → E) (y0 : Fin 29 → E)
    (z0 z1 : AspisR0.ChordGeometry.Point E)
    (hne : z0 ≠ z1) (h0 : ¬ AspisR0.Chord.BaseRational z0)
    (h1 : ¬ AspisR0.Chord.BaseRational z1)
    (opening : List (R0FS.Msg E × R0FS.Chal E)) :
    openingViewZ
      ⟨x, rounds recoverC2 payloads challenges ++
        ((Msg.beforeZ0 y, Chal.circle z0) ::
          (Msg.beforeZ1 y0, Chal.circle z1) :: openingPairsZ opening)⟩ =
      some ⟨R0P.SemSource.openingStmt x (recoverC2 (rootAt2 payloads)).1
        (recoverC2 (rootAt2 payloads)).2 hb
        (fun j => (List.ofFn challenges)[15 + j.val]'(by simp; omega))
        y z0 z1 hne h0 h1, opening⟩ := by
  have hsem : (rounds recoverC2 payloads challenges).length = 25 :=
    rounds_length recoverC2 payloads challenges
  have hcs : (List.ofFn challenges).length = 25 := by simp
  have hparse : semChalsZ (rounds recoverC2 payloads challenges) =
      some (List.ofFn challenges) :=
    semChalsZ_rounds recoverC2 payloads challenges
  have hc2 : c2OfZ (rounds recoverC2 payloads challenges) =
      some (recoverC2 (rootAt2 payloads)) :=
    c2OfZ_rounds recoverC2 payloads challenges
  exact openingViewZ_of_parsed x (rounds recoverC2 payloads challenges)
    (List.ofFn challenges) hsem hcs hparse
    (recoverC2 (rootAt2 payloads)).1 (recoverC2 (rootAt2 payloads)).2 hc2 hb
    y y0 z0 z1 hne h0 h1 opening

#print axioms opening_view_of_payloads

end AspisR1.SemanticPayloadOpeningView
