import OraclePortJoinSplitOrdering

/-! Outer short-circuit transport only. Inner children retain their existing
schedule. This is not an identification with frozen batch_tree. -/
set_option autoImplicit false
namespace AspisR1.OraclePortShortCircuit
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def eager : List (Program Bytes State Bool) → Program Bytes State Bool
  | [] => .done true
  | p::ps => bind p fun b => bind (eager ps) fun c => .done (b && c)

def short : List (Program Bytes State Bool) → Program Bytes State Bool
  | [] => .done true
  | p::ps => bind p fun b => if b then short ps else .done false

theorem verdict (H : Bytes → State) (ps : List (Program Bytes State Bool)) :
    (eval H (short ps)).2 = (eval H (eager ps)).2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [short,eager,eval_bind,eval]
    cases hb : (eval H p).2 <;> simp [hb,ih,eval]

theorem log_prefix (H : Bytes → State) (ps : List (Program Bytes State Bool)) :
    (eval H (short ps)).1 <+: (eval H (eager ps)).1 := by
  induction ps with
  | nil => exact ⟨[],rfl⟩
  | cons p ps ih =>
    simp only [short,eager,eval_bind,eval,List.append_nil]
    cases hb : (eval H p).2
    · simp only [hb,Bool.false_eq_true,if_false,eval,List.append_nil]
      exact ⟨_,rfl⟩
    · simp only [hb,if_true]
      obtain ⟨suffix,eq⟩ := ih
      exact ⟨suffix,by rw [List.append_assoc,eq]⟩

theorem accepted_eq (H : Bytes → State) (ps : List (Program Bytes State Bool))
    (ha : (eval H (short ps)).2 = true) :
    eval H (short ps) = eval H (eager ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases hb : (eval H p).2
    · simp [short,eval_bind,hb,eval] at ha
    · have ht : (eval H (short ps)).2 = true := by
        simpa only [short,eval_bind,hb,if_true,eval] using ha
      simp only [short,eager,eval_bind,hb,if_true,eval,ih ht,
        Bool.true_and,List.append_nil]

#print axioms verdict
#print axioms log_prefix
#print axioms accepted_eq
end AspisR1.OraclePortShortCircuit
