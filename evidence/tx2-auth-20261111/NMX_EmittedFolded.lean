import NMX_FoldedProgram
import NMX_PdaValue
import NMX_QuestionValue
set_option autoImplicit false
noncomputable section
namespace NMX_EmittedFolded
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Replacement for the retired whole-evaluator tactic: the evaluator has
already been discharged by55 checked single-call steps and their folds. Here
only the finite Result/control algebra of the emitted body is normalized. -/
theorem normalized (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_FoldedProgram.normalized ops owners verifier accounts pool outputLane slot =
 NMX_Emitted.auth ops ops.op50 (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
  verifier accounts pool outputLane slot := by
 by_cases count : Slice.len accounts = 7#usize
 · simp only [NMX_FoldedProgram.normalized,NMX_Emitted.auth,count,
    bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
   simp only [NMX_Fold00.v001,
  NMX_Fold00.v002,
  NMX_Fold00.v003,
  NMX_Fold00.v004,
  NMX_Fold00.v005,
  NMX_Fold00.v006,
  NMX_Fold00.v007,
  NMX_Fold00.v008,
  NMX_Fold00.v009,
  NMX_Fold00.v010,
  NMX_Fold01.v011,
  NMX_Fold01.v012,
  NMX_Fold01.v013,
  NMX_Fold01.v014,
  NMX_Fold01.v015,
  NMX_Fold01.v016,
  NMX_Fold01.v017,
  NMX_Fold01.v018,
  NMX_Fold01.v019,
  NMX_Fold01.v020,
  NMX_Fold02.v021,
  NMX_Fold02.v022,
  NMX_Fold02.v023,
  NMX_Fold02.v024,
  NMX_Fold02.v025,
  NMX_Fold02.v026,
  NMX_Fold02.v027,
  NMX_Fold02.v028,
  NMX_Fold02.v029,
  NMX_Fold02.v030,
  NMX_Fold03.v031,
  NMX_Fold03.v032,
  NMX_Fold03.v033,
  NMX_Fold03.v034,
  NMX_Fold03.v035,
  NMX_Fold03.v036,
  NMX_Fold03.v037,
  NMX_Fold03.v038,
  NMX_Fold03.v039,
  NMX_Fold03.v040,
  NMX_Fold04.v041,
  NMX_Fold04.v042,
  NMX_Fold04.v043,
  NMX_Fold04.v044,
  NMX_Fold04.v045,
  NMX_Fold04.v046,
  NMX_Fold04.v047,
  NMX_Fold04.v048,
  NMX_Fold04.v049,
  NMX_Fold04.v050,
  NMX_Fold05.v051,
  NMX_Fold05.v052,
  NMX_Fold05.v053,
  NMX_Fold05.v054,
  NMX_Fold05.v055,
    NMX_PdaMap.try_bind,NMX_PdaValue.raw]
   simp only [tryThen,NMX_QuestionValue.branch,NMX_PdaMap.master,NMX_PdaMap.checkpoint,
    NMX_PdaMap.lane,NMX_PdaValue.mapped,lift,bind_tc_ok]
   rfl
 · simp [NMX_FoldedProgram.normalized,NMX_Emitted.auth,count]

/-- Actual emitted value/control correspondence on every input and every
opaque reply, including Err/fail/div. Allocation-abort interpretation remains
separate, as required by the canonical relational specification. -/
theorem source (ops : Ops) (owners : Owners) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) :
 NMX_ValueLink.erase (eval (NMX_SourceModel.source ops owners)
  (NMX_SourceProgram.auth ops verifier accounts pool outputLane slot) ()) =
 NMX_Emitted.auth ops ops.op50 (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
  verifier accounts pool outputLane slot :=
 (NMX_FoldedProgram.erased ops owners verifier accounts pool outputLane slot).trans
  (normalized ops owners verifier accounts pool outputLane slot)
#print axioms normalized
#print axioms source
end NMX_EmittedFolded
end
