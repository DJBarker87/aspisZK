import R1Z.QueryScanHistorySplit
import R1Z.PhaseSamplerParserBin
import AspisV8R19.R406SamplerWordDistribution

/-! Symbolic law for independent block coins. Reached-history restrictions
are subevents, not conditioning on already revealed future query answers.
This is not a claim that repeated shared-ROM answers are fresh coins. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanIndependentHistory
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R1Z.CouplingR1PBin
  R1Z.QueryScanPrivacyFinal R1Z.PhaseSamplerParserBin
  AspisV8R19.R406SamplerWordDistribution
attribute [local instance] Classical.propDecidable

abbrev Word := Fin (2^18)

def block (b : OracleAnswer) : Fin 8 → Word := (splitBlockEquiv (state b)).2

theorem block_le_words (b : OracleAnswer) :
    blockWords b = List.ofFn (fun j => (block b j).val) := words_value (state b)

theorem block_uniform : MP block := by
  intro f
  have h := mp_equiv (R1J.SamplerLawSpend.stateEquiv.trans splitBlockEquiv)
    (fun p => f p.2)
  have h2 := mp_snd (X := Fin 8 → Fin (2^14)) (Y := Fin 8 → Word) f
  exact h.trans h2

def flatten : (Fin 8 → Fin 8 → Word) ≃ (Fin 64 → Word) where
  toFun q i := q ((finProdFinEquiv (m := 8) (n := 8)).symm i).1 ((finProdFinEquiv (m := 8) (n := 8)).symm i).2
  invFun w k j := w (finProdFinEquiv (k, j))
  left_inv q := by funext k j; simp
  right_inv w := by funext i; simp

def words64 (q : Fin 8 → OracleAnswer) : Fin 64 → Word := flatten (fun k => block (q k))

theorem words64_uniform : MP words64 := by
  intro f
  exact (mp_pi block_uniform 8 (fun q => f (flatten q))).trans (mp_equiv flatten f)

theorem smallRange_mass :
    eventMass (fun w : Fin 64 → Word => AspisR1.QueryScanExhaustion.smallRange w 21) =
      scanProbability := by
  have hc {A : Type} [Fintype A] (E : A → Prop) :
      (Fintype.card {a // E a} : ℚ) = ∑ a : A, if E a then (1 : ℚ) else 0 := by
    simp only [Fintype.card_subtype, Finset.sum_boole]
  have hd : (Fintype.card (Fin 64 → Word) : ℚ) = ((2^18 : ℕ) : ℚ)^64 := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  exact congrArg₂ (fun a b : ℚ => a / b)
    (hc (A := Fin 64 → Word) (fun w => AspisR1.QueryScanExhaustion.smallRange w 21)).symm hd

/-- A history-dependent reachability condition may only reduce the mass of
failure on independent coins. No independence of the reachability event is
needed, and the statement is intentionally not a conditional probability. -/
theorem reached_failure_le (reached : (Fin 8 → OracleAnswer) → Prop) :
    eventMass (fun q => reached q ∧ AspisR1.QueryScanModelFailure.fails (words64 q)) ≤
      scanProbability := by
  apply (eventMass_mono _ (fun q => AspisR1.QueryScanExhaustion.smallRange (words64 q) 21)
    (fun q h => AspisR1.QueryScanModelFailure.failure_smallRange _ h.2)).trans
  have hu := words64_uniform
    (fun w => if AspisR1.QueryScanExhaustion.smallRange w 21 then (1 : ℚ) else 0)
  exact hu.le.trans smallRange_mass.le

/-- Eight attempt coordinates are enough, with no concrete enumeration of
blocks, word arrays or histories. -/
theorem eight_reached_failures_le
    (reached : Fin 8 → (Fin 8 → Fin 8 → OracleAnswer) → Prop) (i : Fin 8) :
    eventMass (fun q : Fin 8 → Fin 8 → OracleAnswer =>
      reached i q ∧ AspisR1.QueryScanModelFailure.fails (words64 (q i))) ≤ scanProbability := by
  apply (eventMass_mono _ (fun q => AspisR1.QueryScanExhaustion.smallRange (words64 (q i)) 21)
    (fun q h => AspisR1.QueryScanModelFailure.failure_smallRange _ h.2)).trans
  have he := mean_eval i
    (fun q => if AspisR1.QueryScanExhaustion.smallRange (words64 q) 21 then (1 : ℚ) else 0)
  have hu := words64_uniform
    (fun w => if AspisR1.QueryScanExhaustion.smallRange w 21 then (1 : ℚ) else 0)
  exact he.le.trans (hu.le.trans smallRange_mass.le)

#print axioms block_le_words
#print axioms block_uniform
#print axioms words64_uniform
#print axioms smallRange_mass
#print axioms reached_failure_le
#print axioms eight_reached_failures_le
end R1Z.QueryScanIndependentHistory
