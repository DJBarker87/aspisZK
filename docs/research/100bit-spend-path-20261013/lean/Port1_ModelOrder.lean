import Port1_CanonicalJoin

/-! Exact no-read scheduling algebra needed between checkpoint resumption and
batch1. This is not a concrete per-body interpretation or frozen2 identity. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_ModelOrder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A total no-read state calculation may move before a batch, while its
acceptance check stays after that batch. Even rejected batch logs are equal. -/
theorem silent_before_batch {A : Type} (silent : Program Bytes State A)
    (batch : Program Bytes State Bool) (check : A → Bool)
    (H : Bytes → State) (value : A) (noRead : eval H silent = ([],value)) :
    eval H (bind batch fun ok => if ok then bind silent (fun a => .done (check a)) else .done false) =
      eval H (bind silent fun a => bind batch fun ok => .done (ok && check a)) := by
  simp only [eval_bind,noRead,eval,List.nil_append,List.append_nil]
  cases h : (eval H batch).2 <;> simp [h,eval_bind,eval,noRead]

/-- Chaining pure query, weight flush and state projection introduces no
reads and transports their actual returned state, rather than choosing one. -/
theorem silent_bind {A B : Type} (p : Program Bytes State A)
    (k : A → Program Bytes State B) (H : Bytes → State) (a : A) (b : B)
    (hp : eval H p = ([],a)) (hk : eval H (k a) = ([],b)) :
    eval H (bind p k) = ([],b) := by simp only [eval_bind,hp,hk,List.nil_append]

/-- Existing body-port hypotheses constrain equality to another arbitrary
interpretation. They are reflexively inhabited for EVERY interpretation;
they alone cannot pin that interpretation to the frozen2 mathematical model. -/
theorem body_joins_refl (model : VTop_OracleCode.Implementation) :
    Port1_DriverSubstitution.BodyJoins model model := by
  have operation : ∀ id, VTop_OracleStages.OperationJoin model model id := by
    intro id A call operation H value accepted
    rfl
  exact ⟨operation 3,operation 4,operation 5,operation 6,operation 7,
    operation 8,operation 9,operation 10,operation 11,operation 12,
    operation 17,operation 18,operation 19⟩

#print axioms silent_before_batch
#print axioms silent_bind
#print axioms body_joins_refl
end AspisR1.Port1_ModelOrder
end
