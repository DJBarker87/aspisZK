import FS2.DuplexTrace

/-! A cardinality bound for parsed-state collisions at addresses in the
already-read domain or at one specified endpoint. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ParsedStateCollision

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.UniformStateFirstHit

variable {M Cv : Type} {L : Nat}

def bad (pred : Addr L → Option State) (Qtot : Nat) (a : Addr L)
    (T : Table (Addr L) State) (f : State) : Prop :=
  (dom T).card < Qtot ∧ ∃ b, (b = a ∨ T b ≠ none) ∧ pred b = some f

theorem density (pred : Addr L → Option State) (Qtot : Nat) (a : Addr L)
    (T : Table (Addr L) State) :
    mean (fun f : State => indicator (bad pred Qtot a T f)) ≤
      (Qtot : ℚ) / (Fintype.card State : ℚ) := by
  classical
  by_cases hsz : (dom T).card < Qtot
  · have hpre := mean_exists_prefix_le (fun f : State => some f)
      (by intro f f' h; exact Option.some.inj h)
      (fun b : Addr L => b = a ∨ T b ≠ none) pred
    have hfilt : ((Finset.univ.filter fun b : Addr L => b = a ∨ T b ≠ none).card : ℚ) ≤
        ((dom T).card : ℚ) + 1 := by
      exact_mod_cast card_filter_insert_le T a
    have hcard : (0 : ℚ) < (Fintype.card State : ℚ) := by
      rw [state_card]
      positivity
    calc mean (fun f : State => indicator (bad pred Qtot a T f))
        = mean (fun f : State => indicator
            (∃ b, (b = a ∨ T b ≠ none) ∧ pred b = some f)) := by
          apply mean_congr
          intro f
          apply indicator_iff
          simp [bad, hsz]
      _ ≤ ((Finset.univ.filter fun b : Addr L => b = a ∨ T b ≠ none).card : ℚ) /
            (Fintype.card State : ℚ) := hpre
      _ ≤ (((dom T).card : ℚ) + 1) / (Fintype.card State : ℚ) :=
            div_le_div_of_nonneg_right hfilt hcard.le
      _ ≤ (Qtot : ℚ) / (Fintype.card State : ℚ) := by
            apply div_le_div_of_nonneg_right _ hcard.le
            have hq : ((dom T).card : ℚ) + 1 ≤ (Qtot : ℚ) := by
              exact_mod_cast Nat.succ_le_of_lt hsz
            linarith
  · have hz : ∀ f : State, indicator (bad pred Qtot a T f) = 0 := by
      intro f
      rw [indicator_iff (q := False), indicator_false]
      exact ⟨fun h => hsz h.1, False.elim⟩
    rw [mean_congr hz, mean_const, state_card]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem mass {X Pf : Type} (pred : Addr L → Option State) (Qtot : Nat)
    (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (hitsBad (bad pred Qtot) emptyTable (eval H (FS2.experiment P V x)).1)) ≤
      (Qtot : ℚ) * ((Qtot : ℚ) / (256 ^ 32 : ℚ)) := by
  classical
  rw [empty_oracle_law (FS2.experiment P V x)
    (fun v => indicator (hitsBad (bad pred Qtot) emptyTable v.1))]
  have hε : (0 : ℚ) ≤ (Qtot : ℚ) / (256 ^ 32 : ℚ) :=
    div_nonneg (by positivity) (by positivity)
  have hdens : ∀ (a : Addr L) (T : Table (Addr L) State),
      mean (fun f => indicator (bad pred Qtot a T f)) ≤
        (Qtot : ℚ) / (256 ^ 32 : ℚ) := by
    intro a T
    have h := density pred Qtot a T
    rw [state_card] at h
    push_cast at h
    exact h
  apply FS.lemmaA (FS2.experiment P V x) emptyTable Qtot (bad pred Qtot) _ hε hdens
  apply firstReadsBound_of_traces
  intro H
  have hc : complete (emptyTable : Table (Addr L) State) H = H := rfl
  rw [hc]
  exact hQ H

#print axioms density
#print axioms mass

end AspisR1.ParsedStateCollision
end
