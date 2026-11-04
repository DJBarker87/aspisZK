import R1Z.QueryScanFirstStopHistory
import R1Z.PhaseProtocolInstanceBin

/-! The constructed ideal experiment has independent transcript-answer coins.
This proves the scan mass on that exact randomness carrier, including any
attempt reachability restriction. It does not assert a source coupling. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanIdealHistory
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R1Z.CouplingR1PBin
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.TranscriptR1
  R1Z.QueryScanPrivacyFinal R1Z.QueryScanIndependentHistory
attribute [local instance] Classical.propDecidable

/-- Split out any injectively indexed set of independent coordinates. -/
def splitCoordinates {I J U : Type} (j : I → J) (hj : Function.Injective j) :
    (J → U) ≃ (I → U) × ({x : J // ¬ ∃ i, j i = x} → U) where
  toFun v := (fun i => v (j i), fun x => v x.val)
  invFun p x := if hx : ∃ i, j i = x then p.1 (Classical.choose hx) else p.2 ⟨x, hx⟩
  left_inv v := by
    funext x
    dsimp only
    split
    · next hx => exact congrArg v (Classical.choose_spec hx)
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      dsimp only
      rw [dif_pos (show ∃ k, j k = j i from ⟨i, rfl⟩)]
      exact congrArg p.1 (hj (Classical.choose_spec (show ∃ k, j k = j i from ⟨i, rfl⟩)))
    · funext x
      dsimp only
      rw [dif_neg x.property]

/-- This mean law is generic in all carrier sizes. -/
theorem coordinates_uniform {I J U : Type} [Fintype I] [Fintype J]
    [Fintype U] [Nonempty U] (j : I → J) (hj : Function.Injective j) :
    MP (fun v : J → U => fun i => v (j i)) := by
  intro f
  have he := mp_equiv (splitCoordinates (U := U) j hj) (fun p => f p.1)
  exact he.trans (mp_fst f)

/-- Transport across extensionally equal finite universes without reducing
the byte-carrier enumeration hidden in an inferred Fintype instance. -/
theorem mean_fintype_transport {A : Type} (fin1 fin2 : Fintype A) (f : A → ℚ) :
    @mean A fin1 f = @mean A fin2 f := by
  have he : @Finset.univ A fin1 = @Finset.univ A fin2 := by
    ext a
    simp only [Finset.mem_univ]
  unfold mean Fintype.card
  rw [he]

def queryCoins {Cm Tab : Type} (c : R1Coins Cm Tab) : Fin 8 → OracleAnswer :=
  fun k => c.1 (.qb k)

theorem queryCoins_uniform {Cm Tab : Type} [Fintype Cm] [Nonempty Cm]
    [Fintype Tab] [Nonempty Tab] : MP (queryCoins (Cm := Cm) (Tab := Tab)) := by
  change MP (fun c : (TRead → OracleAnswer) × ((Fin 3 → OracleAnswer) × Cm × Tab) =>
    fun k => c.1 (.qb k))
  intro f
  have hc := coordinates_uniform (U := OracleAnswer) TRead.qb
    (by intro a b hab; cases hab; rfl) f
  have hp := mp_fst (X := TRead → OracleAnswer)
    (Y := (Fin 3 → OracleAnswer) × Cm × Tab) (fun tr => f (fun k => tr (.qb k)))
  trans mean (fun tr : TRead → OracleAnswer => f (fun k => tr (.qb k)))
  · exact hp
  · convert hc using 1 <;> apply mean_fintype_transport

variable {Cm Tab Tape : Type} [Fintype Cm] [Nonempty Cm] [Fintype Tab] [Nonempty Tab]
  [Fintype Tape] [Nonempty Tape]

/-- These are exactly fsR1P.IdealRand's outer product and retry coordinates. -/
abbrev IdealCoins := (Fin 8 → R1Coins Cm Tab) × (Fin 8 → Tape)

def bad (i : Fin 8) (r : IdealCoins (Cm := Cm) (Tab := Tab) (Tape := Tape)) : Prop :=
  AspisR1.QueryScanModelFailure.fails (words64 (queryCoins (r.1 i)))

theorem ideal_bad_mass (i : Fin 8) :
    eventMass (bad (Cm := Cm) (Tab := Tab) (Tape := Tape) i) ≤ scanProbability := by
  have hm := mp_comp
    (mp_fst (X := Fin 8 → R1Coins Cm Tab) (Y := Fin 8 → Tape))
    (mp_pi (queryCoins_uniform (Cm := Cm) (Tab := Tab)) 8)
  have he := hm (fun q => if AspisR1.QueryScanModelFailure.fails (words64 (q i)) then (1 : ℚ) else 0)
  have hb := eight_reached_failures_le (fun _ _ => True) i
  simp only [true_and] at hb
  exact he.le.trans hb

theorem reached_ideal_bad_mass
    (reached : Fin 8 → IdealCoins (Cm := Cm) (Tab := Tab) (Tape := Tape) → Prop) (i : Fin 8) :
    eventMass (fun r => reached i r ∧ bad i r) ≤ scanProbability :=
  (eventMass_mono _ _ (fun _ h => h.2)).trans (ideal_bad_mass i)

/-- The bad event at the parser's selected endpoint, including fallback and
failure. This is fixed by the model, not selected by a source coupling. -/
def selectedBad (i : Fin 8) (r : IdealCoins (Cm := Cm) (Tab := Tab) (Tape := Tape)) : Prop :=
  let q := queryCoins (r.1 i)
  ∃ count, AspisV8R19.Q22WordScan.finish
    (PhaseSamplerParserBin.scanned (PhaseQueryScanBin.stop PhaseSamplerParserBin.done q) q).1 =
      .error count

theorem selected_bad_mass (i : Fin 8) :
    eventMass (selectedBad (Cm := Cm) (Tab := Tab) (Tape := Tape) i) ≤ scanProbability := by
  apply (eventMass_mono _ (bad i) ?_).trans (ideal_bad_mass i)
  intro r hr
  obtain ⟨count, hf⟩ := hr
  exact QueryScanFirstStopHistory.selected_failure_implies_words_failure _ count hf

theorem reached_selected_bad_mass
    (reached : Fin 8 → IdealCoins (Cm := Cm) (Tab := Tab) (Tape := Tape) → Prop) (i : Fin 8) :
    eventMass (fun r => reached i r ∧ selectedBad i r) ≤ scanProbability :=
  (eventMass_mono _ _ (fun _ h => h.2)).trans (selected_bad_mass i)

#print axioms mean_fintype_transport
#print axioms coordinates_uniform
#print axioms queryCoins_uniform
#print axioms ideal_bad_mass
#print axioms reached_ideal_bad_mass
#print axioms selected_bad_mass
#print axioms reached_selected_bad_mass
end R1Z.QueryScanIdealHistory
