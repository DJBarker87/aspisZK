import Port10AUTH_Node
import Port9OR_P6Levels

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Levels
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem rows {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (fuel : Nat) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    Port9OR_Code.trace (Port10AUTH_Total.dictionary D H) hash (Port9OR_P6Rows.rows fuel s physical i w)=
      eval (rawOracle H) (MultiproofConePhysicalLevels.rows fuel s physical i w) := by
  induction fuel generalizing s i w with
  | zero =>
    by_cases halt : i≥s.n <;>
      simp only [Port9OR_P6Rows.rows,MultiproofConePhysicalLevels.rows,halt,↓reduceIte,
        Port9OR_Code.trace,eval,Port10AUTH_Trace.trace_lift]
  | succ fuel ih =>
    by_cases halt : i≥s.n
    · simp only [Port9OR_P6Rows.rows,MultiproofConePhysicalLevels.rows,if_pos halt,Port9OR_Code.trace,eval]
    · simp only [Port9OR_P6Rows.rows,MultiproofConePhysicalLevels.rows,if_neg halt,
        Port10AUTH_Trace.trace_bind,Port10AUTH_Node.node,MultiproofConePhysicalLevels.bindRun,eval_bind]
      cases h : eval (rawOracle H) (MultiproofConePhysicalProgram.node s physical i w) with
      | mk log result =>
        cases result with
        | fail e => simp only [checked,eval,List.append_nil]
        | div => simp only [checked,eval,List.append_nil]
        | ok out =>
          simp only [checked]
          cases out with
          | Stop stopped => simp only [Port10AUTH_Leaf.pure_trace,eval,List.append_nil]
          | Next next ni nw => rw [ih next ni nw]

theorem level {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (s : reference.Scratch) (physical : Slice U8) :
    Port9OR_Code.trace (Port10AUTH_Total.dictionary D H) hash (Port9OR_P6Levels.level s physical)=
      eval (rawOracle H) (MultiproofConePhysicalLevels.level s physical) := rows D hash H _ s physical _ _

/-- Arbitrary symbolic height. No height18 or recurrence normalization. -/
theorem levels {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (height : Nat) (s : reference.Scratch) (physical : Slice U8) :
    Port9OR_Code.trace (Port10AUTH_Total.dictionary D H) hash (Port9OR_P6Levels.levels height s physical)=
      eval (rawOracle H) (MultiproofConePhysicalLevels.levels height s physical) := by
  induction height generalizing s with
  | zero => rfl
  | succ height ih =>
    simp only [Port9OR_P6Levels.levels,MultiproofConePhysicalLevels.levels,
      Port10AUTH_Trace.trace_bind,level,MultiproofConePhysicalLevels.bindRun,eval_bind]
    cases h : eval (rawOracle H) (MultiproofConePhysicalLevels.level s physical) with
    | mk log result =>
      cases result with
      | fail e => simp only [checked,eval,List.append_nil]
      | div => simp only [checked,eval,List.append_nil]
      | ok out =>
        simp only [checked]
        cases out with
        | Stop stopped => simp only [Port10AUTH_Leaf.pure_trace,eval,List.append_nil]
        | Done next => rw [ih next]

/-- Full actual accepted height observation transported to the raw physical
model, retaining every repeated call and exact returned scratch. -/
theorem accepted {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (height : Nat) (s : reference.Scratch) (physical : Slice U8) (out : reference.Level)
    (success : erase D hash (Port9OR_P6Levels.levels height s physical)=ok out) :
    Port9OR_Code.trace D hash (Port9OR_P6Levels.levels height s physical)=
      eval (rawOracle H) (MultiproofConePhysicalLevels.levels height s physical) :=
  (Port10AUTH_Total.accepted D hash H _ out oracle success).symm.trans (levels D hash H height s physical)

#print axioms rows
#print axioms level
#print axioms levels
#print axioms accepted
end AspisR1.Port10AUTH_Levels
end
