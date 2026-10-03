import AspisV8R19.R452NoRefillProgram
import AspisV8R19.R447SourceInitialBlockLaw

set_option autoImplicit false
namespace AspisV8R19.R453SourceFirstLimbLaw
open MemoizedProgramLaw OracleProgramOps SourceOraclePrograms QM31SamplerProgram
open R452NoRefillProgram R447SourceInitialBlockLaw R445InitialBlockRejectionLaw
open OracleResampling AspisV8PairedCommitment
abbrev State := SourceDuplexStep.State
abbrev Bytes := DuplexFrames.Bytes
noncomputable section

def firstLimbProgram (s : State) : Program Bytes State (Option Nat × Cursor) :=
  bind (squeezeProgram s) (fun p => limbProgram 8 ⟨p.2,p.1,0⟩)

theorem firstLimbProgram_shape (s : State) :
    firstLimbProgram s =
      .ask (DuplexFrames.squeeze (SourceDuplexStep.bytes s)) (fun block =>
        .ask (DuplexFrames.advance (SourceDuplexStep.bytes s)) (fun next =>
          .done ((limbRun (fun _ => next) 8 ⟨next,block,0⟩).2))) := by
  unfold firstLimbProgram squeezeProgram
  simp only [bind]
  congr 1
  funext block
  congr 1
  funext next
  exact limbProgram_no_refill (fun _ => next) 8 ⟨next,block,0⟩
    (by change (0 : Nat) + 8 ≤ 8; omega)

/-- Exact lazy shared-oracle law when both source squeeze addresses are unread.
The unread hypotheses are local obligations, not whole-campaign freshness. -/
theorem first_limb_lazy_mean (s : State) (t : Table Bytes State)
    (hs : t (DuplexFrames.squeeze (SourceDuplexStep.bytes s)) = none)
    (ha : t (DuplexFrames.advance (SourceDuplexStep.bytes s)) = none)
    (f : Option Nat → ℚ) :
    lazyMean (firstLimbProgram s) t (fun v => f v.2.1) =
      mean (fun block : State => f (Option.map Fin.val (initialBlockResult block))) := by
  rw [firstLimbProgram_shape]
  simp only [lazyMean, hs]
  apply mean_congr
  intro block
  have hne := DuplexFrames.cross_disjoint
    (SourceDuplexStep.bytes s) (SourceDuplexStep.bytes s)
  have hmiss : put t (DuplexFrames.squeeze (SourceDuplexStep.bytes s)) block
      (DuplexFrames.advance (SourceDuplexStep.bytes s)) = none := by
    simp [put, Ne.symm hne, ha]
  rw [hmiss]
  simp only [lazyMean]
  simp_rw [actual_initial_limb_value]
  exact mean_const _

theorem first_limb_lazy_failure (s : State) (t : Table Bytes State)
    (hs : t (DuplexFrames.squeeze (SourceDuplexStep.bytes s)) = none)
    (ha : t (DuplexFrames.advance (SourceDuplexStep.bytes s)) = none) :
    lazyMean (firstLimbProgram s) t (fun v => if v.2.1 = none then (1 : ℚ) else 0) =
      (1 / (2147483648 : ℚ)) ^ 8 := by
  rw [first_limb_lazy_mean s t hs ha (fun x => if x = none then (1 : ℚ) else 0)]
  simpa only [Option.map_eq_none_iff] using initial_block_failure

#print axioms firstLimbProgram_shape
#print axioms first_limb_lazy_mean
#print axioms first_limb_lazy_failure
end
end AspisV8R19.R453SourceFirstLimbLaw
