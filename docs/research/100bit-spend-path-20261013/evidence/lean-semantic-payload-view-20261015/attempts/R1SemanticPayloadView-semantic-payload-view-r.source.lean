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

theorem exists_rootAt2 (payloads : (row : Fin 25) → RowPayload row) :
    ∃ root, (payloads ⟨2, by omega⟩).val = .c2Root root := by
  rcases payloads ⟨2, by omega⟩ with ⟨payload, hvalid⟩
  cases payload with
  | empty => simp [validRow] at hvalid
  | c2Root root => exact ⟨root, rfl⟩
  | maskSum value => simp [validRow] at hvalid
  | polynomial coefficients => simp [validRow] at hvalid

noncomputable def rootAt2 (payloads : (row : Fin 25) → RowPayload row) : State :=
  Classical.choose (exists_rootAt2 payloads)

theorem rootAt2_payload (payloads : (row : Fin 25) → RowPayload row) :
    (payloads ⟨2, by omega⟩).val = .c2Root (rootAt2 payloads) :=
  Classical.choose_spec (exists_rootAt2 payloads)

theorem exists_claimAt14 (payloads : (row : Fin 25) → RowPayload row) :
    ∃ value, (payloads ⟨14, by omega⟩).val = .maskSum value := by
  rcases payloads ⟨14, by omega⟩ with ⟨payload, hvalid⟩
  cases payload with
  | empty => simp [validRow] at hvalid
  | c2Root root => simp [validRow] at hvalid
  | maskSum value => exact ⟨value, rfl⟩
  | polynomial coefficients => simp [validRow] at hvalid

noncomputable def claimAt14 (payloads : (row : Fin 25) → RowPayload row) : E :=
  (Classical.choose (exists_claimAt14 payloads)).val

theorem claimAt14_payload (payloads : (row : Fin 25) → RowPayload row) :
    (payloads ⟨14, by omega⟩).val =
      .maskSum (Classical.choose (exists_claimAt14 payloads)) :=
  Classical.choose_spec (exists_claimAt14 payloads)

theorem exists_coeffAt (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
    ∃ coefficients, (payloads ⟨15 + j.val, by omega⟩).val = .polynomial coefficients := by
  rcases payloads ⟨15 + j.val, by omega⟩ with ⟨payload, hvalid⟩
  cases payload with
  | empty => simp [validRow] at hvalid; omega
  | c2Root root => simp [validRow] at hvalid; omega
  | maskSum value => simp [validRow] at hvalid; omega
  | polynomial coefficients => exact ⟨coefficients, rfl⟩

noncomputable def coeffAt (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
    Coefficients := Classical.choose (exists_coeffAt payloads j)

theorem coeffAt_payload (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
    (payloads ⟨15 + j.val, by omega⟩).val = .polynomial (coeffAt payloads j) :=
  Classical.choose_spec (exists_coeffAt payloads j)

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

theorem rounds_getElem? (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E)
    (i : Fin 25) :
    (rounds recoverC2 payloads challenges)[i.val]? =
      some (R0C.SemStatement.Msg.semantic (toMessage recoverC2 (payloads i).val),
        R0C.SemStatement.Chal.semantic (challenges i)) := by
  rw [List.getElem?_eq_getElem (by rw [rounds_length]; exact i.isLt)]
  exact congrArg some (rounds_get recoverC2 payloads challenges i)

theorem toMessage_rootAt2 (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) :
    toMessage recoverC2 (payloads ⟨2, by omega⟩).val =
      .base (.h1 (recoverC2 (rootAt2 payloads)).1 (recoverC2 (rootAt2 payloads)).2) := by
  rw [rootAt2_payload]
  rfl

theorem toMessage_claimAt14 (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) :
    toMessage recoverC2 (payloads ⟨14, by omega⟩).val = .maskSum (claimAt14 payloads) := by
  rw [claimAt14_payload]
  rfl

theorem toMessage_coeffAt (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
    toMessage recoverC2 (payloads ⟨15 + j.val, by omega⟩).val =
      .base (.roundPoly (polynomial (coeffAt payloads j))) := by
  rw [coeffAt_payload]
  rfl

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
  have h2 := rounds_get recoverC2 payloads challenges ⟨2, by omega⟩
  have hmap := congrArg (fun q : MsgZ E × ChalZ E => (unmaskMsg q.1, q.2)) h2
  have hlenBase : (baseRoundsZ (rounds recoverC2 payloads challenges)).length = 25 := by
    simp [baseRoundsZ, rounds_length]
  have hbaseVal :
      (baseRoundsZ (rounds recoverC2 payloads challenges))[2]'(by omega) =
        (R0C.SemStatement.Msg.semantic (.h1
          (recoverC2 (rootAt2 payloads)).1 (recoverC2 (rootAt2 payloads)).2),
          R0C.SemStatement.Chal.semantic (challenges ⟨2, by omega⟩)) := by
    simpa [baseRoundsZ, List.getElem_map, unmaskMsg, unmaskSem, toMessage_rootAt2] using hmap
  change c2Of (baseRoundsZ (rounds recoverC2 payloads challenges)) = _
  unfold c2Of
  rw [List.getElem?_eq_getElem (by rw [hlenBase]; omega)]
  rw [hbaseVal]

theorem claimOf_rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    claimOf (rounds recoverC2 payloads challenges) = some (claimAt14 payloads) := by
  have hget := rounds_getElem? recoverC2 payloads challenges ⟨14, by omega⟩
  unfold claimOf
  rw [hget]
  rw [toMessage_claimAt14]

theorem semPolysZ_rounds (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) :
    semPolysZ (rounds recoverC2 payloads challenges) =
      some (fun j => polynomial (coeffAt payloads j)) := by
  classical
  have hlen := rounds_length recoverC2 payloads challenges
  have hslot (j : Fin 10) :
      ((rounds recoverC2 payloads challenges)[15 + j.val]'(by omega)).1 =
        R0C.SemStatement.Msg.semantic (.base (.roundPoly (polynomial (coeffAt payloads j)))) := by
    have h := rounds_get recoverC2 payloads challenges ⟨15 + j.val, by omega⟩
    have h' := congrArg Prod.fst h
    rw [toMessage_coeffAt] at h'
    exact h'
  simp [semPolysZ, rounds_length, hslot]

theorem polynomial_degree (recoverC2 : State → InitialWord × InitialWord)
    (payloads : (row : Fin 25) → RowPayload row) (challenges : Fin 25 → E) (j : Fin 10) :
    ((polynomial (coeffAt payloads j) : E[X])).natDegree ≤ 27 :=
  SemanticCoefficientCodec.polynomial_natDegree_le _

#print axioms rounds_length
#print axioms rounds_get
#print axioms rounds_getElem?
#print axioms semChalsZ_rounds
#print axioms c2OfZ_rounds
#print axioms claimOf_rounds
#print axioms semPolysZ_rounds
#print axioms polynomial_degree

end AspisR1.SemanticPayloadView
end
