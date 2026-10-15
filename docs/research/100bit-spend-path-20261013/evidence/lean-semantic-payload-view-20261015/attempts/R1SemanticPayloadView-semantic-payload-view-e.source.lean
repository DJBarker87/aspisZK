import R1SemanticRecordCodec
import R0P.MaskView

/-! Explicit view of typed semantic payloads as the old 25-row semantic
message parser input.  The C2 word-pair is supplied by a representation
callback; this file makes no extraction or source-correspondence claim. -/
set_option autoImplicit false

noncomputable section
namespace AspisR1.SemanticPayloadView

open R0P R0P.Mask R0P.SemSource R0P.SemDegree Polynomial
open AspisR1.SemanticRecordCodec AspisR1.SemanticCoefficientCodec

abbrev E := AspisWideTower.WideExact
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev InitialWord := AspisPool.AlgorithmicCircleDecoderV7.InitialWord E

def toMessage (recoverC2 : State → InitialWord × InitialWord) :
    Payload → SemMsgZ E
  | .empty => .base .none
  | .c2Root root => .base (.h1 (recoverC2 root).1 (recoverC2 root).2)
  | .maskSum value => .maskSum value.val
  | .polynomial coefficients => .base (.roundPoly (polynomial coefficients))

def pairs (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row)
    (challenges : Fin 25 → E) : List (SemMsgZ E × E) :=
  List.ofFn fun i => (toMessage recoverC2 (payloads i).val, challenges i)

def rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row)
    (challenges : Fin 25 → E) : List (MsgZ E × ChalZ E) :=
  (pairs recoverC2 payloads challenges).map fun q =>
    (R0C.SemStatement.Msg.semantic q.1, R0C.SemStatement.Chal.semantic q.2)

def rootAt2 (payloads : (row : Fin 25) → RowPayload row) : State :=
  match payloads ⟨2, by omega⟩ with
  | ⟨.empty, h⟩ => False.elim (by simp [validRow] at h)
  | ⟨.c2Root root, _⟩ => root
  | ⟨.maskSum _, h⟩ => False.elim (by simp [validRow] at h)
  | ⟨.polynomial _, h⟩ => False.elim (by simp [validRow] at h)

def claimAt14 (payloads : (row : Fin 25) → RowPayload row) : E :=
  match payloads ⟨14, by omega⟩ with
  | ⟨.empty, h⟩ => False.elim (by simp [validRow] at h)
  | ⟨.c2Root _, h⟩ => False.elim (by simp [validRow] at h)
  | ⟨.maskSum value, _⟩ => value.val
  | ⟨.polynomial _, h⟩ => False.elim (by simp [validRow] at h)

def coeffAt (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
    Coefficients :=
  match payloads ⟨15 + j.val, by omega⟩ with
  | ⟨.empty, h⟩ => False.elim (by simp [validRow] at h; omega)
  | ⟨.c2Root _, h⟩ => False.elim (by simp [validRow] at h; omega)
  | ⟨.maskSum _, h⟩ => False.elim (by simp [validRow] at h; omega)
  | ⟨.polynomial coefficients, _⟩ => coefficients

theorem rounds_get (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E)
    (i : Fin 25) :
    (rounds recoverC2 payloads challenges)[i.val]'i.isLt =
      (R0C.SemStatement.Msg.semantic (toMessage recoverC2 (payloads i).val),
       R0C.SemStatement.Chal.semantic (challenges i)) := by
  simp only [rounds, List.getElem_map, pairs, List.getElem_ofFn]

theorem rounds_length (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    (rounds recoverC2 payloads challenges).length = 25 := by
  simp [rounds, pairs]

theorem semChalsZ_rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    semChalsZ (rounds recoverC2 payloads challenges) =
      some (List.ofFn challenges) := by
  simpa [rounds, pairs] using
    (semChalsZ_of_pairs (pairs recoverC2 payloads challenges))

theorem c2OfZ_rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    c2OfZ (rounds recoverC2 payloads challenges) =
      some (recoverC2 (rootAt2 payloads)) := by
  simp [c2OfZ, baseRoundsZ, rounds_get, rootAt2, toMessage, unmaskMsg, unmaskSem]

theorem claimOf_rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    claimOf (rounds recoverC2 payloads challenges) = some (claimAt14 payloads) := by
  simp [claimOf, rounds_get, claimAt14, toMessage]

theorem semPolysZ_rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    semPolysZ (rounds recoverC2 payloads challenges) =
      some (fun j => polynomial (coeffAt payloads j)) := by
  classical
  unfold semPolysZ
  rw [dif_pos (rounds_length recoverC2 payloads challenges)]
  apply congrArg some
  funext j
  rw [rounds_get]
  simp [toMessage, coeffAt]

theorem polynomial_degree (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) (j : Fin 10) :
    ((polynomial (coeffAt payloads j) : E[X])).natDegree ≤ 27 :=
  SemanticCoefficientCodec.polynomial_natDegree_le _

#print axioms rounds_length
#print axioms rounds_get
#print axioms semChalsZ_rounds
#print axioms c2OfZ_rounds
#print axioms claimOf_rounds
#print axioms semPolysZ_rounds
#print axioms polynomial_degree

end AspisR1.SemanticPayloadView
end
