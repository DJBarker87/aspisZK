import SdkC_GlobalRecovery
import SdkC_NativeNode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Accounting
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

/-- Branch-complete source budget. Pure failures stop; successful hash replies
may select any continuation. Repeated inputs are charged individually here. -/
def Bounded {A : Type} : Nat → SdkC_Source.Code A → Prop
  | _, .done _ => True
  | n, .step r next => match r with
    | .ok a => Bounded n (next a)
    | .fail _ => True
    | .div => True
  | n, .read _ next => 0 < n ∧ ∀ d, Bounded (n-1) (next d)

/-- ALL source syscall attempts, including an aborting final attempt. -/
theorem attempts {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : SdkC_Source.Code A) (before : SdkC_Source.Log) (n : Nat) (budget : Bounded n code) :
    (SdkC_Source.run hashv code before).2.length ≤ before.length+n := by
  induction code generalizing before n with
  | done a => simp only [SdkC_Source.run]; omega
  | step r next ih =>
    cases r with
    | ok a => exact ih a before n budget
    | fail e => simp only [SdkC_Source.run]; omega
    | div => simp only [SdkC_Source.run]; omega
  | read parts next ih =>
    have positive := budget.1
    cases actual : hashv parts with
    | fail e => simp only [SdkC_Source.run,actual,List.length_append,List.length_singleton]; omega
    | div => simp only [SdkC_Source.run,actual,List.length_append,List.length_singleton]; omega
    | ok d =>
      have rest := ih d (before ++ [⟨parts,.ok d⟩]) (n-1) (budget.2 d)
      simp only [SdkC_Source.run,actual]
      simp only [List.length_append,List.length_singleton] at rest
      omega

/-- Distinct ROM reads are bounded by all attempted source syscalls. -/
theorem first_reads {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : SdkC_Source.Code A) (n : Nat) (budget : Bounded n code) :
    firstReads emptyTable (SdkC_Source.readLog (SdkC_Source.run hashv code []).2) ≤ n := by
  exact (VerifierCallBudget.firstReads_le_length emptyTable _).trans
    ((SdkC_Source.read_count _).trans (by simpa using attempts hashv code [] n budget))

/-- The ideal experiment has the SAME branch-complete source query cap. -/
theorem ideal_reads {A : Type} (code : SdkC_Source.Code A) (n : Nat) (budget : Bounded n code)
    (H : Bytes → State) :
    (eval H (SdkC_Oracle.program code)).1.length ≤ n := by
  induction code generalizing n with
  | done a => exact Nat.zero_le n
  | step r next ih =>
    cases r with
    | fail e => exact Nat.zero_le n
    | div => exact Nat.zero_le n
    | ok a => exact ih a n budget
  | read parts next ih =>
    have positive := budget.1
    have rest := ih (AspisV8R19.SqueezeOracleBridge.encodeState (H
      (AspisV8R19.SqueezeOracleBridge.flatten parts))) (n-1) (budget.2 _)
    simp only [SdkC_Oracle.program,eval,List.length_cons]
    omega

/-- Explicit security loss, with the bound instantiated by source syntax. -/
theorem collision_bound {A : Type} (code : SdkC_Source.Code A) (Q : Nat) (budget : Bounded Q code) :
    lazyMean (SdkC_Oracle.program code) emptyTable
      (fun view => AspisV8R19.CausalFirstHitUnionBound.indicator
        (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv Q view)) ≤
      6 * (Q : ℚ)^2 / (256^32 : ℚ) := by
  apply SdkC_GlobalRecovery.collision_bound code Q
  intro H
  exact (VerifierCallBudget.firstReads_le_length emptyTable _).trans (ideal_reads code Q budget H)

/-- Installed source leaf attempts at most one syscall, on every input and
outcome; no width or successful hash premise is needed for this bound. -/
theorem leaf_budget (kind : Usize) (opening : Slice U8) :
    Bounded 1 (Port4B_LeafCode.code kind opening) := by
  unfold Port4B_LeafCode.code Port4B_LeafCode.codeFor
  repeat' first
  | (solve | trivial)
  | split
  | constructor
  | intro d
  | (fail_if_no_progress simp only [Bounded])
  all_goals omega

#print axioms attempts
#print axioms first_reads
#print axioms ideal_reads
#print axioms collision_bound
#print axioms leaf_budget
end AspisR1.SdkC_Accounting
end
