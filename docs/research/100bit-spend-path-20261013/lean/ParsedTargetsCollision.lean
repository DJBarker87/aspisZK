import R1ParsedStateCollision

/-! Union bounds for a fixed finite family of parsed-state target
predictions. The cardinality `B` is symbolic; this module does not choose a
protocol-specific value for it. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ParsedTargetsCollision

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.UniformStateFirstHit

variable {M Cv : Type} {L : Nat}

def bad {B : Nat} (pred : Fin B → Addr L → Option State) (Qtot : Nat)
    (a : Addr L) (T : Table (Addr L) State) (f : State) : Prop :=
  ∃ j : Fin B, ParsedStateCollision.bad (pred j) Qtot a T f

theorem density {B : Nat} (pred : Fin B → Addr L → Option State)
    (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State) :
    mean (fun f : State => indicator (bad pred Qtot a T f)) ≤
      (B : ℚ) * (Qtot : ℚ) / (Fintype.card State : ℚ) := by
  classical
  have h := mean_firstHit_union_le
    (fun j : Fin B => ParsedStateCollision.bad (pred j) Qtot a T)
    (fun _ => (Qtot : ℚ) / (Fintype.card State : ℚ))
    (fun j => ParsedStateCollision.density (pred j) Qtot a T)
  calc
    _ = mean (fun f : State => indicator
        (∃ j : Fin B, ParsedStateCollision.bad (pred j) Qtot a T f)) := rfl
    _ ≤ ∑ _j : Fin B, (Qtot : ℚ) / (Fintype.card State : ℚ) := h
    _ = (B : ℚ) * (Qtot : ℚ) / (Fintype.card State : ℚ) := by
      simp [Finset.sum_const, Fintype.card_fin, div_eq_mul_inv, mul_assoc]

theorem mass {B : Nat} {X Pf : Type}
    (pred : Fin B → Addr L → Option State) (Qtot : Nat)
    (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (hitsBad (bad pred Qtot) emptyTable
        (eval H (FS2.experiment P V x)).1)) ≤
      (B : ℚ) * (Qtot : ℚ)^2 / (256^32 : ℚ) := by
  classical
  rw [empty_oracle_law (FS2.experiment P V x)
    (fun v => indicator (hitsBad (bad pred Qtot) emptyTable v.1))]
  have hε : (0 : ℚ) ≤
      (B : ℚ) * (Qtot : ℚ) / (256 ^ 32 : ℚ) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg Qtot)
    · positivity
  have hdens : ∀ (a : Addr L) (T : Table (Addr L) State),
      mean (fun f => indicator (bad pred Qtot a T f)) ≤
        (B : ℚ) * (Qtot : ℚ) / (256 ^ 32 : ℚ) := by
    intro a T
    have h := density pred Qtot a T
    rw [state_card] at h
    push_cast at h
    exact h
  have hN : FirstReadsBound (FS2.experiment P V x)
      (emptyTable : Table (Addr L) State) Qtot := by
    apply firstReadsBound_of_traces
    intro H
    have hc : complete (emptyTable : Table (Addr L) State) H = H := rfl
    rw [hc]
    exact hQ H
  have hlemma := FS.lemmaA (FS2.experiment P V x) emptyTable Qtot
    (bad pred Qtot) (B * (Qtot : ℚ) / (256^32 : ℚ)) hε hdens hN
  calc
    _ ≤ (Qtot : ℚ) * ((B : ℚ) * (Qtot : ℚ) / (256^32 : ℚ)) := hlemma
    _ = (B : ℚ) * (Qtot : ℚ)^2 / (256^32 : ℚ) := by ring

#print axioms density
#print axioms mass

end AspisR1.ParsedTargetsCollision
end
