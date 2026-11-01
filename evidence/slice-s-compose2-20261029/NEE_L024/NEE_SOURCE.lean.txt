import NEE_ValidatorMutation
set_option autoImplicit false
noncomputable section
namespace NEE_OracleCallDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
open NED_ValidatorTrace NEE_ValidatorMutation
open NEE_ValidatorOracle

def TailShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.lane (parts s).2.2.2.2.1] ∨
  xs = [.lane (parts s).2.2.2.2.1,.late (common s).lane_transition NBN_LateResult.zero]

def Shape (s : Statement) (xs : List Call) : Prop :=
  xs = [] ∨ xs = [.payment s] ∨
  xs = [.payment s,.lane (parts s).2.2.2.2.1] ∨
  xs = [.payment s,.lane (parts s).2.2.2.2.1,.late (common s).lane_transition NBN_LateResult.zero]

theorem tail_shape (pay : Pay) (lane : Lane) (late : Late) (s : Statement) : TailShape s (NEE_ValidatorOracle.tail pay lane late s).2 := by
  unfold NEE_ValidatorOracle.tail
  dsimp only
  cases h : lane (parts s).2.2.2.2.1 with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok r => cases r with
    | Err e => simp only [h]; exact Or.inl rfl
    | Ok l =>
      simp only [h]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem bindings_shape (pay : Pay) (lane : Lane) (late : Late) (s : Statement) :
    (NEE_ValidatorOracle.bindings pay lane late s).2 = [] ∨ TailShape s (NEE_ValidatorOracle.bindings pay lane late s).2 := by
  unfold NEE_ValidatorOracle.bindings
  repeat' first | split | exact Or.inl rfl | exact Or.inr (tail_shape pay lane late s)

theorem shape (pay : Pay) (lane : Lane) (late : Late) (s : Statement) : Shape s (NEE_ValidatorOracle.run pay lane late s).2 := by
  unfold NEE_ValidatorOracle.run
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · cases h : pay s with
      | fail e => simp only [h]; exact Or.inr (Or.inl rfl)
      | div => simp only [h]; exact Or.inr (Or.inl rfl)
      | ok r => cases r with
        | Err e => simp only [h]; exact Or.inr (Or.inl rfl)
        | Ok bytes =>
          simp only [h]
          rcases bindings_shape pay lane late s with none | one | two
          · rw [none]; exact Or.inr (Or.inl rfl)
          · rw [one]; exact Or.inr (Or.inr (Or.inl rfl))
          · rw [two]; exact Or.inr (Or.inr (Or.inr rfl))

/-- A logged late call has the SAME full record and fixed local output width.
The whole root need not accept: an error returned by that call is retained. -/
theorem late_domain (pay : Pay) (lane : Lane) (late : Late) (s : Statement) (arg : NBN_LateSummary.Statement) (out : Slice U8)
    (reached : Call.late arg out ∈ (NEE_ValidatorOracle.run pay lane late s).2) :
    arg = (common s).lane_transition ∧ out = NBN_LateResult.zero ∧ out.length = 1520 := by
  rcases shape pay lane late s with none | one | two | three
  · simp only [none,List.not_mem_nil] at reached
  · simp only [one,List.mem_singleton,reduceCtorEq] at reached
  · simp only [two,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at reached
  · simp only [three,List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.late.injEq] at reached
    obtain ⟨rfl,rfl⟩ := reached
    refine ⟨rfl,rfl,?_⟩
    simp only [NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
    rfl

theorem payment_same (pay : Pay) (lane : Lane) (late : Late) (s : Statement) (arg : Statement)
    (reached : Call.payment arg ∈ (NEE_ValidatorOracle.run pay lane late s).2) : arg = s := by
  rcases shape pay lane late s with none | one | two | three <;>
    simp_all only [List.mem_cons,List.not_mem_nil,
      reduceCtorEq,false_or,or_false,Call.payment.injEq]

/-- Every lane call uses the same nullifier, even for arbitrary failing
child replies. This is a caller-domain fact, not a child success premise. -/
theorem lane_same (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (arg : Array U32 8#usize)
    (reached : Call.lane arg ∈ (NEE_ValidatorOracle.run pay lane late s).2) :
    arg = (parts s).2.2.2.2.1 := by
  rcases shape pay lane late s with none | one | two | three <;>
    simp_all only [List.mem_cons,List.not_mem_nil,
      reduceCtorEq,false_or,or_false,Call.lane.injEq]

#print axioms lane_same
#print axioms tail_shape
#print axioms bindings_shape
#print axioms shape
#print axioms late_domain
#print axioms payment_same
end NEE_OracleCallDomains
