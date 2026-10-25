import Port12COUNT_Potential
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_Rows
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain MultiproofConeLevelIteration Port12COUNT_Potential
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Exact ordered effects through checked Code bind, including outer errors. -/
theorem eval_join {A B Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (code : Code A) (k : A → Code B) :
    eval H (Port9OR_Code.program D hash (code >>= k)) =
      let first := eval H (Port9OR_Code.program D hash code)
      match first.2 with
      | .ok a => let rest := eval H (Port9OR_Code.program D hash (k a))
                 (first.1 ++ rest.1,rest.2)
      | .fail e => (first.1,.fail e)
      | .div => (first.1,.div) := by
  change eval H (Port9OR_Code.program D hash (CheckpointBytes5Effect.bind code k)) = _
  induction code with
  | done a => rfl
  | step r f ih => cases r <;> simp only [CheckpointBytes5Effect.bind,Port9OR_Code.program,
      VTop_OracleCode.continueWith,eval,ih]
  | read parts f ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [CheckpointBytes5Effect.bind,Port9OR_Code.program,call,eval]
    | div => simp only [CheckpointBytes5Effect.bind,Port9OR_Code.program,call,eval]
    | ok digest =>
      simp only [CheckpointBytes5Effect.bind,Port9OR_Code.program,call,eval,ih]
      split <;> rfl

def retained {A : Type} (post : A → Nat) : Result A → Nat
  | .ok a => post a
  | _ => 0

/-- Actual physical rows, every fuel and every native outcome. No successful
output progress is used on an error path to discard its final read. -/
theorem rows {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (physical : Slice U8) (fuel : Nat)
    (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w) :
    let out := eval H (Port9OR_Code.program D hash (Port9OR_P6Rows.rows fuel s physical i w))
    out.1.length + retained (levelPost physical) out.2 ≤ credit physical s i w := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [Port9OR_P6Rows.rows]
    split
    · rename_i halt
      have hi : i.val=s.n.val := by have := domain.2.2.1; change i.val≥s.n.val at halt;omega
      simp only [Port9OR_Code.program,eval,retained,levelPost,credit,List.length_nil,Nat.zero_add,hi]
      simp
    · simp only [liftResult,Port9OR_Code.program,VTop_OracleCode.continueWith,eval,retained,List.length_nil,Nat.zero_add]
      omega
  | succ fuel ih =>
    simp only [Port9OR_P6Rows.rows]
    split
    · rename_i halt
      have hi : i.val=s.n.val := by have := domain.2.2.1; change i.val≥s.n.val at halt;omega
      simp only [Port9OR_Code.program,eval,retained,levelPost,credit,List.length_nil,Nat.zero_add,hi]
      simp
    · rename_i halt
      have active : i.val<s.n.val := by change ¬i.val≥s.n.val at halt;omega
      have localCost := Port12COUNT_Potential.count D hash H
        (Port9OR_P6Node.node s physical i w) (rowPost physical) (credit physical s i w)
        (node_funded physical s i w domain active)
      rw [eval_join]
      cases ran : eval H (Port9OR_Code.program D hash (Port9OR_P6Node.node s physical i w)) with
      | mk log result =>
        simp only [ran] at localCost
        cases result with
        | fail e => exact localCost
        | div => exact localCost
        | ok out =>
          have sourceRan := Port9OR_P6Node.node_value D hash s physical i w H
          rw [ran] at sourceRan
          have progress := Port9OR_P6Progress.node_progress (Port9OR_Code.native D H) hash physical s i w
            domain active out sourceRan.symm
          cases out with
          | Stop stopped =>
            change (log ++ []).length + 0 ≤ _
            simpa only [rowPost,List.append_nil,Nat.add_zero] using localCost
          | Next next ni nw =>
            have tail := ih next ni nw progress.2.1
            simp only [rowPost] at localCost
            simp only [List.length_append]
            omega

#print axioms eval_join
#print axioms rows
end AspisR1.Port12COUNT_Rows
end
