import R1Z.QueryScanSharedHistoryObstruction
import R1Z.QueryScanIdealHistory

/-! Even unconditioned, a uniform shared-ROM scan from a fixed input state
has a self-loop contribution. This is a scan-subrun result, not a lower bound
on the complete release game's differently distributed starting state. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanSharedHistoryMass
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R1Z.CouplingR1PBin
  R1Z.QueryScanSharedHistoryObstruction R1Z.PhaseSamplerParserBin
  R1Z.PhaseQueryScanBin R1Z.QueryScanPrivacyFinal
attribute [local instance] Classical.propDecidable

theorem eval_uniform {A U : Type} [Fintype A] [DecidableEq A] [Fintype U] [Nonempty U]
    (a : A) : MP (fun t : A → U => t a) := by
  intro f
  have he := mp_equiv (R1Z.LazyTable.splitAt (U := U) a) (fun p => f p.1)
  exact he.trans (mp_fst f)

theorem point_mass {U : Type} [Fintype U] (u : U) :
    eventMass (fun v : U => v = u) = 1 / (Fintype.card U : ℚ) := by
  unfold eventMass mean
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem eval_point_mass {A U : Type} [Fintype A] [DecidableEq A] [Fintype U] [Nonempty U]
    (a : A) (u : U) : eventMass (fun t : A → U => t a = u) = 1 / (Fintype.card U : ℚ) := by
  have hu := eval_uniform (U := U) a (fun v => if v = u then (1 : ℚ) else 0)
  exact hu.trans (point_mass u)

theorem self_loop_mass (bound : ℕ) (hbound : 33 ≤ bound) :
    eventMass (fun tab : R1Z.RomFiniteBin.Address bound → OracleAnswer =>
      R1Z.RomFiniteBin.lookup bound tab (advanceAddress 0) = 0) =
      1 / (Fintype.card OracleAnswer : ℚ) := by
  let a : R1Z.RomFiniteBin.Address bound :=
    ⟨advanceAddress 0, (loop_addresses_in_domain bound hbound 0).2⟩
  have he (tab : R1Z.RomFiniteBin.Address bound → OracleAnswer) :
      R1Z.RomFiniteBin.lookup bound tab (advanceAddress 0) = tab a := by
    unfold R1Z.RomFiniteBin.lookup
    rw [show R1Z.RomFiniteBin.decode bound (advanceAddress 0) = some a from
      R1Z.RomFiniteBin.decode_encode bound a]
  simp only [he]
  exact eval_point_mass a (0 : OracleAnswer)

theorem uniform_shared_scan_failure_lower_bound (bound : ℕ) (hbound : 33 ≤ bound) :
    1 / (Fintype.card OracleAnswer : ℚ) ≤
    eventMass (fun tab : R1Z.RomFiniteBin.Address bound → OracleAnswer =>
      ∃ count, AspisV8R19.Q22WordScan.finish (scanned
        (stop done (queryBlocks (R1Z.RomFiniteBin.lookup bound tab) 0))
        (queryBlocks (R1Z.RomFiniteBin.lookup bound tab) 0)).1 = .error count) := by
  rw [← self_loop_mass bound hbound]
  exact eventMass_mono _ _ (fun tab ht => shared_loop_finish_fails _ _ ht)

/-- Count the bytes symbolically; no universe of answers is reduced. -/
theorem answer_cardinality : Fintype.card OracleAnswer = 2^256 := by
  have hA : ∀ j : Fintype OracleAnswer, @Fintype.card OracleAnswer j = 2^256 := fun j =>
    (congrArg (@Fintype.card OracleAnswer) (Subsingleton.elim j _)).trans R1Z.LensR1.card_ans
  exact hA _

theorem scanProbability_lt_self_loop_mass :
    scanProbability < 1 / (Fintype.card OracleAnswer : ℚ) := by
  rw [answer_cardinality, Nat.cast_pow, Nat.cast_ofNat]
  apply scan_probability_le.trans_lt
  apply one_div_lt_one_div_of_lt (by positivity)
  exact pow_lt_pow_right₀ (by norm_num) (by omega : 256 < 486)

theorem uniform_shared_scan_not_independent_bound (bound : ℕ) (hbound : 33 ≤ bound) :
    ¬ eventMass (fun tab : R1Z.RomFiniteBin.Address bound → OracleAnswer =>
      ∃ count, AspisV8R19.Q22WordScan.finish (scanned
        (stop done (queryBlocks (R1Z.RomFiniteBin.lookup bound tab) 0))
        (queryBlocks (R1Z.RomFiniteBin.lookup bound tab) 0)).1 = .error count) ≤ scanProbability := by
  intro hh
  exact not_le_of_gt scanProbability_lt_self_loop_mass
    ((uniform_shared_scan_failure_lower_bound bound hbound).trans hh)

#print axioms eval_uniform
#print axioms point_mass
#print axioms eval_point_mass
#print axioms self_loop_mass
#print axioms uniform_shared_scan_failure_lower_bound
#print axioms answer_cardinality
#print axioms scanProbability_lt_self_loop_mass
#print axioms uniform_shared_scan_not_independent_bound
end R1Z.QueryScanSharedHistoryMass
