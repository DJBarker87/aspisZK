import R0P.MaskView
import R0P.MaskD2

/-! The masked semantic classifier. The polynomial degree guard begins at
15; eta at 14 parses a scalar claim and never uses a polynomial degree guard. -/
set_option autoImplicit false
namespace R0P.Mask
open FS FS2 R0C.SemStatement R0P R0P.SemSource R0P.SemD3Glue R0P.Sumcheck Polynomial
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.SourceDuplexStep
noncomputable section
attribute [local instance] Classical.propDecidable

section Generic
variable {K : Type} [Field K]

/-- Keep the concrete predicate atomic at finite filters (G19). -/
def alphaSomeBad {T : Type} (ts : Finset T) (G : T → (Fin 10 → K) → K)
    (p : K[X]) (j : Fin 10) (pref : Fin j.val → K) (c : K) : Prop :=
  ∃ t ∈ ts, alphaRound 27 10 (G t) (fun _ => p) j pref c

theorem alphaSomeBad_card {T : Type} [Fintype K] (ts : Finset T)
    (G : T → (Fin 10 → K) → K) (p : K[X]) (hp : p.natDegree ≤ 27)
    (j : Fin 10) (pref : Fin j.val → K) :
    (Finset.univ.filter (alphaSomeBad ts G p j pref)).card ≤ ts.card * 27 := by
  classical
  let per : T → Finset K := fun t =>
    Finset.univ.filter (alphaRound 27 10 (G t) (fun _ => p) j pref)
  have hsub : Finset.univ.filter (alphaSomeBad ts G p j pref) ⊆ ts.biUnion per := by
    intro c hc
    obtain ⟨t, ht, hb⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
  calc
    _ ≤ (ts.biUnion per).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ ts, (per t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ ts, 27 := Finset.sum_le_sum (fun t _ => alphaRound_card 27 10 (G t) _ j pref hp)
    _ = ts.card * 27 := by simp

def currentPolyZ (sm : SemMsgZ K) : K[X] :=
  match unmaskSem sm with
  | .roundPoly p => p
  | _ => 0

theorem currentPolyZ_degree (sm : SemMsgZ K) (h : degreeOK (unmaskSem sm)) :
    (currentPolyZ sm).natDegree ≤ 27 := by
  unfold currentPolyZ
  cases he : unmaskSem sm with
  | none => simp
  | h1 h g => simp
  | roundPoly p => simpa only [he, degreeOK] using h

variable [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- All data in each branch is fixed before the current challenge. -/
def semanticBadZ {Sfield : Fin 29 → Subfield K} {F : Subfield K}
    (maskPoly : (Fin 10 → K) → K) (B : PackBasis F)
    (P : Prefix K K (TypedContext K Sfield) (SemMsgZ K)) (sm : SemMsgZ K) (c : K) : Prop :=
  (15 ≤ P.rounds.length → degreeOK (unmaskSem sm)) ∧
  if h14 : P.rounds.length < 14 then
    semanticBad B ⟨P.statement, baseRoundsZ P.rounds⟩ (unmaskSem sm) c
  else if P.rounds.length = 14 then
    match sm, semChalsZ P.rounds with
    | .maskSum claim, some cs =>
        etaSomeBad (candidates P.statement (baseRoundsZ P.rounds) .none)
          (fun t => originalTotal P.statement.pub B t (fun j => cs.getD j.val 0))
          claim (maskTotal maskPoly) c
    | _, _ => False
  else if h25 : P.rounds.length < 25 then
    match semChalsZ P.rounds, claimOf P.rounds with
    | some cs, some _ =>
        alphaSomeBad (candidates P.statement (baseRoundsZ P.rounds) .none)
          (fun t => virtualPolyZ maskPoly P.statement.pub B t
            (fun j => cs.getD j.val 0) (cs.getD 14 0))
          (currentPolyZ sm) ⟨P.rounds.length - 15, by omega⟩
          (fun j => cs.getD (15 + j.val) 0) c
    | _, _ => False
  else False
end Generic

/-- Transfer the per-candidate degree-27 root count through semChal. -/
theorem alphaSomeBad_semChal_mass {T : Type} (ts : Finset T)
    (G : T → (Fin 10 → SemE) → SemE) (p : SemE[X]) (hp : p.natDegree ≤ 27)
    (j : Fin 10) (pref : Fin j.val → SemE) :
    mean (fun s : State => indicator (alphaSomeBad ts G p j pref (semChal s))) ≤
      (ts.card * 27 : Nat) * ((1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4) := by
  let bad : Finset SemE := Finset.univ.filter (alphaSomeBad ts G p j pref)
  have hmem (s : State) : alphaSomeBad ts G p j pref (semChal s) ↔ semChal s ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mean_congr (fun s => indicator_iff (hmem s))]
  apply (semChal_event bad).trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast alphaSomeBad_card ts G p hp j pref
  · exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg) (pow_nonneg (Nat.cast_nonneg _) _)

#print axioms alphaSomeBad_card
#print axioms currentPolyZ_degree
#print axioms semanticBadZ
#print axioms alphaSomeBad_semChal_mass
end
end R0P.Mask
