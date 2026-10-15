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
  match hrow : (payloads ⟨2, by omega⟩).val with
  | .empty => by
      have h := (payloads ⟨2, by omega⟩).property
      simp [validRow] at h
      omega
  | .c2Root root => root
  | .maskSum value => by
      have h := (payloads ⟨2, by omega⟩).property
      simp [validRow] at h
      omega
  | .polynomial coefficients => by
      have h := (payloads ⟨2, by omega⟩).property
      simp [validRow] at h
      omega

theorem rootAt2_payload (payloads : (row : Fin 25) → RowPayload row) :
    (payloads ⟨2, by omega⟩).val = .c2Root (rootAt2 payloads) := by
  have h := (payloads ⟨2, by omega⟩).property
  cases hrow : (payloads ⟨2, by omega⟩).val with
  | empty => simp [validRow] at h
  | c2Root root => simp [rootAt2, hrow]
  | maskSum value => simp [validRow] at h
  | polynomial coefficients => simp [validRow] at h

def claimPayloadAt14 (payloads : (row : Fin 25) → RowPayload row) : LowWide :=
  match hrow : (payloads ⟨14, by omega⟩).val with
  | .empty => by
      have h := (payloads ⟨14, by omega⟩).property
      simp [validRow] at h
      omega
  | .c2Root root => by
      have h := (payloads ⟨14, by omega⟩).property
      simp [validRow] at h
      omega
  | .maskSum value => value
  | .polynomial coefficients => by
      have h := (payloads ⟨14, by omega⟩).property
      simp [validRow] at h
      omega

def claimAt14 (payloads : (row : Fin 25) → RowPayload row) : E :=
  (claimPayloadAt14 payloads).val

theorem claimAt14_payload (payloads : (row : Fin 25) → RowPayload row) :
    (payloads ⟨14, by omega⟩).val = .maskSum (claimPayloadAt14 payloads) := by
  have h := (payloads ⟨14, by omega⟩).property
  cases hrow : (payloads ⟨14, by omega⟩).val with
  | empty => simp [validRow] at h
  | c2Root root => simp [validRow] at h
  | maskSum value => simp [claimPayloadAt14, hrow]
  | polynomial coefficients => simp [validRow] at h

def coeffAt (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) : Coefficients :=
  match hrow : (payloads ⟨15 + j.val, by omega⟩).val with
  | .empty => by
      have h := (payloads ⟨15 + j.val, by omega⟩).property
      simp [validRow] at h
      omega
  | .c2Root root => by
      have h := (payloads ⟨15 + j.val, by omega⟩).property
      simp [validRow] at h
      omega
  | .maskSum value => by
      have h := (payloads ⟨15 + j.val, by omega⟩).property
      simp [validRow] at h
      omega
  | .polynomial coefficients => coefficients

theorem coeffAt_payload (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
    (payloads ⟨15 + j.val, by omega⟩).val = .polynomial (coeffAt payloads j) := by
  have h := (payloads ⟨15 + j.val, by omega⟩).property
  cases hrow : (payloads ⟨15 + j.val, by omega⟩).val with
  | empty => simp [validRow] at h; omega
  | c2Root root => simp [validRow] at h; omega
  | maskSum value => simp [validRow] at h; omega
  | polynomial coefficients => simp [coeffAt, hrow]

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
  have hlenBase : (baseRoundsZ (rounds recoverC2 payloads challenges)).length = 25 := by
    simp [baseRoundsZ, rounds_length]
  have hbaseVal :
      (baseRoundsZ (rounds recoverC2 payloads challenges))[2]'(by omega) =
        (R0C.SemStatement.Msg.semantic (.h1
          (recoverC2 (rootAt2 payloads)).1 (recoverC2 (rootAt2 payloads)).2),
          R0C.SemStatement.Chal.semantic (challenges ⟨2, by omega⟩)) := by
    have h2 := rounds_get recoverC2 payloads challenges ⟨2, by omega⟩
    have hmsg := congrArg Prod.fst h2
    have hmsg' : (rounds recoverC2 payloads challenges)[2].1 =
        (R0C.SemStatement.Msg.semantic
          (toMessage recoverC2 (payloads ⟨2, by omega⟩).val)) := by
      simpa using hmsg
    have hchal := congrArg Prod.snd h2
    have hchal' : (rounds recoverC2 payloads challenges)[2].2 =
        R0C.SemStatement.Chal.semantic (challenges ⟨2, by omega⟩) := by
      simpa using hchal
    simp only [baseRoundsZ, List.getElem_map]
    rw [hmsg', hchal', toMessage_rootAt2]
    simp [unmaskMsg, unmaskSem]
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

theorem polynomial_degree (payloads : (row : Fin 25) → RowPayload row) (j : Fin 10) :
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
