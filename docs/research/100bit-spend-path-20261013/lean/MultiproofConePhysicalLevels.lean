import MultiproofConePhysicalProgram

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalLevels
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def bindRun {α β : Type} (p : Run α) (next : α → Run β) : Run β :=
  bind p (fun result => checked result next)

def rows : Nat → reference.Scratch → Slice U8 → Usize → Usize → Run reference.Level
  | 0,s,_,i,w => .done (if i≥s.n then .ok (.Done {s with n:=w}) else .div)
  | fuel+1,s,physical,i,w =>
    if i≥s.n then .done (.ok (.Done {s with n:=w})) else
    bindRun (node s physical i w) fun out => match out with
      | .Stop stopped => .done (.ok (.Stop stopped))
      | .Next after ni nw => rows fuel after physical ni nw

def level (s : reference.Scratch) (physical : Slice U8) : Run reference.Level :=
  rows s.n.val s physical 0#usize 0#usize

def levels : Nat → reference.Scratch → Slice U8 → Run reference.Level
  | 0,s,_ => .done (.ok (.Done s))
  | height+1,s,physical => bindRun (level s physical) fun out => match out with
      | .Stop stopped => .done (.ok (.Stop stopped))
      | .Done after => levels height after physical

theorem bindRun_result {α β : Type} (H : Address → Digest) (p : Run α) (next : α → Run β) :
    (eval H (bindRun p next)).2 =
      (do let x ← (eval H p).2; (eval H (next x)).2) := by
  simp only [bindRun,eval_bind,checked_result]

/-- The physical Program iterates the exact extracted node; the actual oracle
answer returned by each ask is threaded through every subsequent scratch read. -/
theorem rows_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (fuel : Nat) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    (eval H (rows fuel s physical i w)).2 =
      MultiproofConeNodeIteration.rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w := by
  induction fuel generalizing s i w with
  | zero => rfl
  | succ fuel ih =>
    simp only [rows,MultiproofConeNodeIteration.rows]
    by_cases halt : i≥s.n
    · simp only [halt,if_true,eval]
    · simp only [halt,if_false,bindRun_result,node_result D hash H law]
      cases eq : reference.binary_step D hash s physical i w with
      | fail e => rfl
      | div => rfl
      | ok out =>
        simp only [bind_tc_ok]
        cases out with
        | Stop stopped => rfl
        | Next after ni nw => exact ih after ni nw

theorem level_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (s : reference.Scratch) (physical : Slice U8) (domain : Domain physical s) :
    (eval H (level s physical)).2=reference.level_rows D hash s physical 0#usize 0#usize := by
  have total : HashTotal D hash := fun input => ⟨H input,law input⟩
  have dom : RowDomain physical s 0#usize 0#usize := ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  exact (rows_result D hash H law s.n.val s physical _ _).trans
    (rows_eq_extracted D hash total physical s.n.val s _ _ dom (by simp)).symm

/-- Height induction connects the instrumented physical carrier to the actual
extracted levels. No complete-level/source-log equation is a hypothesis. -/
theorem levels_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (height : Nat) (s : reference.Scratch) (physical : Slice U8) (domain : Domain physical s) :
    (eval H (levels height s physical)).2=
      iterate (fun s => reference.level_rows D hash s physical 0#usize 0#usize) height s := by
  induction height generalizing s with
  | zero => rfl
  | succ height ih =>
    simp only [levels,iterate,bindRun_result,level_result D hash H law s physical domain]
    cases eq : reference.level_rows D hash s physical 0#usize 0#usize with
    | fail e => rfl
    | div => rfl
    | ok out =>
      simp only [bind_tc_ok]
      cases out with
      | Stop stopped => rfl
      | Done after =>
        exact ih after (level_preserve D hash (fun input => ⟨H input,law input⟩) physical s after domain eq)

theorem eighteen_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (s : reference.Scratch) (physical : Slice U8) (domain : Domain physical s) :
    (eval H (levels 18 s physical)).2=reference.levels D hash s physical 18#u32 := by
  rw [levels_eq_iteration D hash physical 18#u32 (by decide) s]
  exact levels_result D hash H law 18 s physical domain

#print axioms bindRun_result
#print axioms rows_result
#print axioms level_result
#print axioms levels_result
#print axioms eighteen_result
end AspisR1.MultiproofConePhysicalLevels
