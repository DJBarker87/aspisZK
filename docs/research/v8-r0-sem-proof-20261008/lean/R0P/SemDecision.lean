import R0P.SemView
import R0P.LaneMap

/-! Lead: the terminal at an arbitrary point and the B2 `decision`.

The ported families take openings and a selector vector; at a Boolean row
these are `rowOpenings`/`rowSel`, at a general point the claims and the
multilinear selector weights (`Selectors::boxed_at_point`). `laneAt` is the
θ-lane vector at (openings, h1, selector); `laneOf` is its Boolean-row
instance (`laneOf_eq_laneAt`, by unfolding). `terminalValue` is
`terminal_parts(...).0` (T:1285–1310): `eq(zc, point)·Σθⁱ laneᵢ + μ·h1 +
μ²·(1 − active)·h1`. `decision` checks the ten sumcheck rounds against
claim 0 with the terminal as the final value, then the opening decision
through `openingView`. -/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 R0C.SemStatement Polynomial Sumcheck
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R19.MemoizedProgramLaw
open AspisR0.Chord AspisR0.ChordGeometry AspisR0.Opening

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

/-- `scalarLaneRow` with explicit openings and selector. -/
def scalarLaneAt (pub : Public K) (o : Openings K) (sel : Sel K) (i : Nat) : K :=
  if i < 12 then
    (scheduleFamily.residuals pub o sel).getD i 0 +
      (occupancyFamily.residuals pub o sel).getD i 0
  else if i < 32 then (scheduleFamily.residuals pub o sel).getD i 0
  else if i < 49 then (pathFamily.residuals pub o sel).getD (i - 32) 0
  else if i < 84 then (valueFamily.residuals pub o sel).getD (i - 49) 0
  else if i < 92 then (digestFamily.residuals pub o sel).getD (i - 84) 0
  else if i < 94 then (assetFamily.residuals pub o sel).getD (i - 92) 0
  else 0

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem scalarLaneRow_eq_at (pub : Public K) (t : Trace K) (b : Fin 1024) (i : Nat) :
    scalarLaneRow pub t b i = scalarLaneAt pub (rowOpenings t b) (rowSel b) i := rfl

/-- The 29 θ-lanes at (openings, h1, selector), in `laneOf`'s order. -/
def laneAt (pub : Public K) (lam chi : K) {F : Subfield K} (B : PackBasis F)
    (o : Openings K) (h1 : K) (sel : Sel K) : Fin 29 → K := fun i =>
  if i.val < 4 then ((poseidonPackedFamily B).residuals pub o sel).getD i.val 0
  else if i.val < 28 then pack4 B (fun j => scalarLaneAt pub o sel (4 * (i.val - 4) + j.val))
  else (copyFamily.residuals pub lam chi o h1 sel).getD 0 0

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem laneOf_eq_laneAt (pub : Public K) (t : Trace K) (lam chi : K) {F : Subfield K}
    (B : PackBasis F) (i : Fin 29) (bits : Fin 10 → Bool) :
    laneOf t pub lam chi B i bits =
      laneAt pub lam chi B (rowOpenings t (rowOf bits)) (t 26 (rowOf bits)) (rowSel (rowOf bits)) i := by
  unfold laneOf laneAt semanticPackedLane
  split
  · rfl
  · split
    · rfl
    · rfl

/-- T:1201–1213, `equality_value`. -/
def eqValue (left right : Fin 10 → K) : K :=
  ∏ c : Fin 10, (1 - left c - right c + left c * right c + left c * right c)

/-- The selector vector at a point: R0's `eqWeight` on the R0-ordered point. -/
def selAt (α : Fin 10 → K) : Sel K := eqWeight (toR0 α)

/-- The copy-active selector at the point (T:1303, `copy_active`). -/
def activeAt (α : Fin 10 → K) : K := copyActiveLiteral (copySelectors (selAt α))

/-- T:1285–1310: `terminal_parts(...).0` at claims `y` and point `α`. -/
def terminalValue (pub : Public K) (lam chi θ μ : K) (zc : Fin 10 → K) {F : Subfield K}
    (B : PackBasis F) (y : Fin 3 → Fin 29 → K) (α : Fin 10 → K) : K :=
  let o : Openings K := ⟨fun c => y 0 (Fin.castLE (by omega) c), fun c => y 1 (Fin.castLE (by omega) c),
    fun c => y 2 (Fin.castLE (by omega) c)⟩
  let h1 := y 0 26
  eqValue zc α * (∑ i : Fin 29, θ ^ i.val * laneAt pub lam chi B o h1 (selAt α) i) +
    μ * h1 + μ * μ * ((1 - activeAt α) * h1)

/-- The ten sumcheck rounds of a parsed transcript: round polynomials from
the messages at rounds 14–23, challenges α. Boundary checks from claim 0,
degree ≤ 27, final value equal to the terminal at the claims. -/
def sumcheckChecks (pub : Public K) {F : Subfield K} (B : PackBasis F)
    (cs : List K) (hcs : cs.length = 24) (polys : Fin 10 → K[X])
    (y : Fin 3 → Fin 29 → K) : Prop :=
  let lam := cs[0]'(by omega)
  let chi := cs[1]'(by omega)
  let θ := cs[2]'(by omega)
  let zc : Fin 10 → K := fun j => cs[3 + j.val]'(by omega)
  let μ := cs[13]'(by omega)
  let α : Fin 10 → K := fun j => cs[14 + j.val]'(by omega)
  (∀ j : Fin 10, (polys j).natDegree ≤ 27) ∧
  (polys 0).eval 0 + (polys 0).eval 1 = 0 ∧
  (∀ j : Fin 9, (polys j.succ).eval 0 + (polys j.succ).eval 1 =
    (polys j.castSucc).eval (α j.castSucc)) ∧
  (polys 9).eval (α 9) = terminalValue pub lam chi θ μ zc B y α

/-- Round polynomials of the 24 semantic rounds (rounds 14–23). -/
def semPolys : List (Msg K K (SemMsg K) × Chal K K) → Option (Fin 10 → K[X])
  | rounds =>
    if h : rounds.length = 24 then
      let get : Fin 10 → Option K[X] := fun j =>
        match (rounds[14 + j.val]'(by omega)).1 with
        | .semantic (.roundPoly p) => some p
        | _ => Option.none
      if hall : ∀ j, (get j).isSome then some (fun j => (get j).get (hall j)) else Option.none
    else Option.none

/-- B2's `decision`: the semantic checks and the opening decision. -/
def decision {F : Subfield K} (B : PackBasis F)
    (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) (m : Msg K K (SemMsg K)) : Bool := by
  classical
  exact decide (∃ (Q : FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K))
    (cs : List K) (hcs : cs.length = 24) (polys : Fin 10 → K[X]) (om : R0FS.Msg K),
    openingView P = some Q ∧ semChals (P.rounds.take 24) = some cs ∧
    semPolys (P.rounds.take 24) = some polys ∧
    sumcheckChecks P.statement.pub B cs hcs polys Q.statement.pointClaims ∧
    m = .opening om ∧ R0FS.decision Q om = true)

#print axioms laneOf_eq_laneAt
#print axioms decision
end
end R0P.SemSource
