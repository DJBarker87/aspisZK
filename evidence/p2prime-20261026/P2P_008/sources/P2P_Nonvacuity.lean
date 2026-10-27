import P2P_Charge
import Hiq_CleanWorld
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_Nonvacuity
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- The no-collision branch is inhabited; this does not assert acceptance
or a joint fixture of all retained native/source/frozen3 assumptions. -/
theorem exists_clean {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ 0+1921) :
    ∃ H : Bytes → State,
      ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv 2965
        (eval H (Hiq_RecordedJoint.program source project select)) ∧
      R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1
        (select (eval H source).2).2 := by
  have small : F3T_Numeric.accountLoss 0 < 1 := by norm_num [F3T_Numeric.accountLoss]
  obtain ⟨H,clean⟩ := Hiq_CleanWorld.exists_clean _ _
    ((F3T_AccountCharge.bound source project select 0 budget).trans_lt small)
  refine ⟨H,clean,?_⟩
  rcases P2P_Charge.binding_or_collision source project select 0 budget H with bad | good
  · exact False.elim (clean bad)
  · exact good

theorem identical_pair (H : Bytes → State) (written : R9PoolRuntimeBinding.Inputs) :
    R9PoolRuntimeBinding.P2Prime H written written := fun _ => ⟨rfl,rfl⟩

#print axioms exists_clean
#print axioms identical_pair
end AspisR1.P2P_Nonvacuity
end
