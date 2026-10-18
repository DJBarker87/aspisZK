import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Congr

namespace R1SumcheckCausality

/-- A ten-coordinate evaluation point after the current round sample and the
complete remaining assignment have overwritten the suffix, as in
`host_sumcheck::prove_sumcheck` (current round is included in the overwrite). -/
def overwriteRoundPoint {X : Type} (point : Fin 10 → X) (round : Nat)
    (sample : X) (suffix : Fin 10 → X) (i : Fin 10) : X :=
  if i.val < round then point i else if i.val = round then sample else suffix i

/-- Agreement on the prefix observed before a round. -/
def SamePrefix {X : Type} (round : Nat) (p p' : Fin 10 → X) : Prop :=
  ∀ i, i.val < round → p i = p' i

theorem overwriteRoundPoint_eq {X : Type} (round : Nat)
    (p p' suffix : Fin 10 → X) (sample : X)
    (hp : SamePrefix round p p') (i : Fin 10) :
    overwriteRoundPoint p round sample suffix i =
      overwriteRoundPoint p' round sample suffix i := by
  unfold overwriteRoundPoint
  by_cases hpre : i.val < round
  · simp [hpre, hp i hpre]
  · by_cases hcur : i.val = round
    · simp [hpre, hcur]
    · simp [hpre, hcur]

/-- The source loop's mathematical payload: for each of the 28 interpolation
samples, aggregate oracle values over assignments to the entire remaining
suffix, interpolate the resulting sample vector, then encode it. -/
def roundPayload {X Y Poly Bytes : Type} (round : Nat)
    (samples : List X) (assignments : List (Fin 10 → X))
    (oracle : (Fin 10 → X) → Y) (aggregate : List Y → Y)
    (interpolate : List Y → Poly) (encode : Poly → Bytes)
    (point : Fin 10 → X) : Bytes :=
  encode (interpolate (samples.map fun sample =>
    aggregate (assignments.map fun suffix => oracle (overwriteRoundPoint point round sample suffix))))

theorem roundPayload_suffix_irrelevant {X Y Poly Bytes : Type} (round : Nat)
    (samples : List X) (assignments : List (Fin 10 → X))
    (oracle : (Fin 10 → X) → Y) (aggregate : List Y → Y)
    (interpolate : List Y → Poly) (encode : Poly → Bytes)
    (point point' : Fin 10 → X) (hp : SamePrefix round point point') :
    roundPayload round samples assignments oracle aggregate interpolate encode point =
      roundPayload round samples assignments oracle aggregate interpolate encode point' := by
  unfold roundPayload
  congr 2
  apply List.map_congr_left
  intro sample hs
  congr 1
  apply List.map_congr_left
  intro suffix hsuffix
  apply congrArg oracle
  funext i
  exact overwriteRoundPoint_eq round point point' suffix sample hp i

/-- Deterministic row framing preserves the payload's prefix independence.
The source `r1_wire::record` checks row/length, then prefixes a fixed header
and copies the payload. -/
def frameRow {Bytes : Type} (header : Bytes) (append : Bytes → Bytes → Bytes)
    (payload : Bytes) : Bytes := append header payload

theorem framedRound_suffix_irrelevant {X Y Poly Bytes : Type}
    (round : Nat) (samples : List X) (assignments : List (Fin 10 → X))
    (oracle : (Fin 10 → X) → Y) (aggregate : List Y → Y)
    (interpolate : List Y → Poly) (encode : Poly → Bytes)
    (header : Bytes) (append : Bytes → Bytes → Bytes)
    (point point' : Fin 10 → X) (hp : SamePrefix round point point') :
    frameRow header append
      (roundPayload round samples assignments oracle aggregate interpolate encode point) =
    frameRow header append
      (roundPayload round samples assignments oracle aggregate interpolate encode point') := by
  simp [frameRow, roundPayload_suffix_irrelevant round samples assignments oracle aggregate interpolate encode point point' hp]

#print axioms roundPayload_suffix_irrelevant
#print axioms framedRound_suffix_irrelevant

end R1SumcheckCausality
