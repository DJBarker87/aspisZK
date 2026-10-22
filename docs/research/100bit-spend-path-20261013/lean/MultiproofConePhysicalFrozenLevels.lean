import MultiproofConePhysicalSourceLevel
import MultiproofConeLiveBatch

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConePhysicalFrozenLevels
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport MultiproofConePhysicalViews
open MultiproofConePhysicalSourceLevel MultiproofConeLivePreservation
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open OraclePortFrozenOrder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def project (physical : Slice U8) : Result reference.Level → Option (Live × Bytes)
  | .ok (.Done s) => some (live s 0 s.n.val,remaining physical s.«at»)
  | _ => none

/-- Accepted physical/log refinement by height induction. Per-level scratch
content and oracle observations are the proved concrete facts, not premises. -/
theorem levels_join {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (physical : Slice U8) (height : Nat) (s final : reference.Scratch) (domain : Domain physical s)
    (sorted : MultiproofConeLiveOrder.Strict (keys s) 0 s.n.val)
    (success : iterate (fun s => reference.level_rows D hash s physical 0#usize 0#usize) height s=ok (.Done final)) :
    ∃ rawLog,
      eval (rawOracle H) (MultiproofConePhysicalLevels.levels height s physical)=(rawLog,ok (.Done final)) ∧
      eval H (runLevels height (live s 0 s.n.val) (remaining physical s.«at»)) =
        (rawLog.map (fun e => (flatten e.1,decodeState e.2)),some (live final 0 final.n.val,remaining physical final.«at»)) := by
  induction height generalizing s with
  | zero => cases success;exact ⟨[],rfl,rfl⟩
  | succ height ih =>
    simp only [iterate] at success
    cases eq : reference.level_rows D hash s physical 0#usize 0#usize with
    | fail e => simp only [eq,bind_tc_fail] at success;cases success
    | div => simp only [eq,bind_tc_div] at success;cases success
    | ok out =>
      rw [eq] at success
      simp only [bind_tc_ok] at success
      cases out with
      | Stop stopped => cases success
      | Done after =>
        have total : HashTotal D hash := fun input => ⟨rawOracle H input,law input⟩
        obtain ⟨front,physicalStep,modelStep⟩ := level_join D hash H law physical s after domain sorted eq
        obtain ⟨tail,physicalTail,modelTail⟩ := ih after
          (level_preserve D hash total physical s after domain eq)
          (level_sorted D hash total physical s after domain sorted eq) success
        refine ⟨front++tail,?_,?_⟩
        · simp only [MultiproofConePhysicalLevels.levels,MultiproofConePhysicalLevels.bindRun,
            eval_bind,physicalStep,MultiproofConePhysicalProgram.checked,physicalTail]
        · simp only [runLevels,eval_bind,modelStep,modelTail,List.map_append]

/-- The accepted physical scratch/log is transported to the exact frozen
ordered height-18 program, with all actual request/answer observations. This
is a multiproof-level theorem, excluding leaf/count/padding/root/caller cuts. -/
theorem accepted_eighteen {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (physical : Slice U8) (s final : reference.Scratch) (domain : Domain physical s)
    (sorted : MultiproofConeLiveOrder.Strict (keys s) 0 s.n.val)
    (success : reference.levels D hash s physical 18#u32=ok (.Done final)) :
    eval H (bind (transport (MultiproofConePhysicalLevels.levels 18 s physical))
      (fun result => .done (project physical result))) =
    eval H (runLevels 18 (live s 0 s.n.val) (remaining physical s.«at»)) := by
  rw [levels_eq_iteration D hash physical 18#u32 (by decide) s] at success
  obtain ⟨rawLog,source,target⟩ := levels_join D hash H law physical 18 s final domain sorted success
  rw [eval_bind,transport_observation,source]
  simp only [eval,project,List.append_nil]
  exact target.symm

#print axioms levels_join
#print axioms accepted_eighteen
end AspisR1.MultiproofConePhysicalFrozenLevels
end
