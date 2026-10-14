import R1MerkleChildTargets
import R1CommitmentRootTargets
import R1ParsedTargetsCollision
import FS2.DuplexTrace

/-! A finite ten-target family combining the eight Merkle child readers and
the two commitment-root readers. This only combines existing predictors and
their generic union bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CombinedMerkleTargets

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.UniformStateFirstHit

variable {L : Nat}

def pred (j : Fin 10) (a : Addr L) : Option State :=
  if h : j.val < 8 then
    MerkleChildTargets.pred ⟨j.val, h⟩ a
  else
    CommitmentRootTargets.pred ⟨j.val - 8, by omega⟩ a

theorem pred_child (j : Fin 8) (a : Addr L) :
    pred ⟨j.val, by omega⟩ a = MerkleChildTargets.pred j a := by
  unfold pred
  have hj : j.val < 8 := j.isLt
  simp only [dif_pos hj]

theorem pred_root (j : Fin 2) (a : Addr L) :
    pred ⟨8 + j.val, by omega⟩ a = CommitmentRootTargets.pred j a := by
  unfold pred
  have hj : ¬ 8 + j.val < 8 := by omega
  simp only [dif_neg hj]
  congr 1
  apply Fin.ext
  simp

theorem bad_equiv (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State)
    (f : State) :
    ParsedTargetsCollision.bad pred Qtot a T f ↔
      (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot a T f ∨
       ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot a T f) := by
  unfold ParsedTargetsCollision.bad
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : j.val < 8
    · left
      let i : Fin 8 := ⟨j.val, h⟩
      have hpred : pred (L := L) j = MerkleChildTargets.pred (L := L) i := by
        have hz : (⟨i.val, by omega⟩ : Fin 10) = j := by
          apply Fin.ext
          rfl
        funext b
        rw [← hz]
        exact pred_child i b
      rw [hpred] at hj
      exact ⟨i, hj⟩
    · right
      let i : Fin 2 := ⟨j.val - 8, by omega⟩
      have hz : (⟨8 + i.val, by omega⟩ : Fin 10) = j := by
        apply Fin.ext
        dsimp [i]
        omega
      have hpred : pred (L := L) j = CommitmentRootTargets.pred (L := L) i := by
        rw [← hz]
        funext b
        exact pred_root i b
      rw [hpred] at hj
      exact ⟨i, hj⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · let j : Fin 10 := ⟨i.val, by omega⟩
      have hpred : pred (L := L) j = MerkleChildTargets.pred (L := L) i := by
        have hz : (⟨i.val, by omega⟩ : Fin 10) = j := by
          apply Fin.ext
          rfl
        funext b
        rw [← hz]
        exact pred_child i b
      refine ⟨j, ?_⟩
      rw [hpred]
      exact hi
    · let j : Fin 10 := ⟨8 + i.val, by omega⟩
      have hpred : pred (L := L) j = CommitmentRootTargets.pred (L := L) i := by
        have hz : (⟨8 + i.val, by omega⟩ : Fin 10) = j := by
          apply Fin.ext
          rfl
        funext b
        rw [← hz]
        exact pred_root i b
      refine ⟨j, ?_⟩
      rw [hpred]
      exact hi

theorem mass {X Pf : Type} (Qtot : Nat)
    (P : Program (Addr L) State Pf)
    (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (hitsBad (ParsedTargetsCollision.bad pred Qtot) emptyTable
        (eval H (FS2.experiment P V x)).1)) ≤
      (10 : ℚ) * (Qtot : ℚ)^2 / (256^32 : ℚ) := by
  simpa [pred] using
    (ParsedTargetsCollision.mass (B := 10) pred Qtot P V x hQ)

#print axioms pred_child
#print axioms pred_root
#print axioms bad_equiv
#print axioms mass

end AspisR1.CombinedMerkleTargets
end
