import F3T_AccountCharge
import OracleProgramLawExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3W_CollisionFree
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
attribute [local instance] Classical.propDecidable

/-- Used only for a checked obstruction, not an accepted-run fixture. -/
theorem exists_clean {A : Type} (p : Program Bytes State A)
    (event : View Bytes State A → Prop)
    (small : lazyMean p emptyTable (fun v=>indicator (event v))<1) :
    ∃ H : Bytes → State, ¬event (eval H p) := by
  by_contra missing
  have every : ∀ H : Bytes → State,event (eval H p) := by
    simpa only [not_exists,not_not] using missing
  have one := OracleProgramLawExt.lazyMean_eq_of_eval p (.done ())
    (fun v=>indicator (event v)) (fun _=>1) (by
      intro H
      simp only [indicator,every H,ite_true])
  have unit : lazyMean (Program.done () : Program Bytes State Unit) emptyTable (fun _=>1)=1 := rfl
  rw [unit] at one
  rw [one] at small
  exact lt_irrefl _ small

theorem account_clean {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (budget : ∀ H,firstReads emptyTable (eval H source).1≤0+1921) :
    ∃ H : Bytes → State,
      ¬BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (0+2965)
        (eval H (Hiq_RecordedJoint.program source project select)) := by
  have bound := F3T_AccountCharge.bound source project select 0 budget
  have small : F3T_Numeric.accountLoss 0<1 := by norm_num [F3T_Numeric.accountLoss]
  exact exists_clean _ _ (lt_of_le_of_lt bound small)

#print axioms exists_clean
#print axioms account_clean
end AspisR1.F3W_CollisionFree
end
