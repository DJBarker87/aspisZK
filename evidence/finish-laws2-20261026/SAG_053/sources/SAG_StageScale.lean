import Stage2FinishBody
import SAG_Quarter
import SAQ_WideABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_StageScale
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

/-- Actual native wide scalar body, with explicit nominal carrier conversion. -/
def mulM (claim : E) (scalar : M) : Result E := do
  let value ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (SAQ_WideABI.toW claim) scalar
  ok (SAQ_WideABI.fromW value)

theorem from_decode (x : AspisR1CurrentWide.Proof.E) :
    CheckpointBytes5Output.ofE (SAQ_WideABI.fromW x) = AspisR1CurrentWide.Proof.decodeWide x := by
  rw [SAQ_WideABI.w_decode]
  rfl

theorem value (claim rhs : E) (scalar : M) (success : mulM claim scalar = ok rhs) :
    CheckpointBytes5Output.ofE rhs = CheckpointBytes5Output.ofE claim *
      SAG_UnrestrictedScale.wideScalarEmbedding scalar := by
  unfold mulM at success
  cases run : AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (SAQ_WideABI.toW claim) scalar with
  | fail error => simp only [run,bind_tc_fail] at success; cases success
  | div => simp only [run,bind_tc_div] at success; cases success
  | ok actual =>
    simp only [run,bind_tc_ok] at success
    have same : SAQ_WideABI.fromW actual = rhs := Result.ok.inj success
    rw [←same,from_decode,SAQ_WideABI.w_decode]
    exact (SAG_UnrestrictedScale.wide_mul_m31_success _ actual scalar run).2

def install {W : Type} (seed : FinishOps W) : FinishOps W :=
  {seed with quarter := ok 536870912#u32, mulM := mulM}

theorem quarter {W : Type} (seed : FinishOps W) (m : M) (claim rhs : E)
    (quarterRun : (install seed).quarter = ok m)
    (multiply : (install seed).mulM claim m = ok rhs) :
    CheckpointBytes5Output.ofE rhs = RoundPairing.quarter * CheckpointBytes5Output.ofE claim := by
  have same : 536870912#u32 = m := Result.ok.inj quarterRun
  subst m
  have h := value claim rhs 536870912#u32 multiply
  rw [SAG_Quarter.source_scalar,mul_comm] at h
  exact h

#print axioms from_decode
#print axioms value
#print axioms quarter
end AspisR1.SAG_StageScale
end
