import NED_EncoderTrace
set_option autoImplicit false
noncomputable section
namespace NED_EncoderCallDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
open NED_EncoderTrace

def LateShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.late (common s).lane_transition NBN_LateResult.zero] ∨
  xs = [.late (common s).lane_transition NBN_LateResult.zero,.payment s]
def AnchorShape (s : Statement) (xs : List Call) : Prop :=
  xs = [.digest (common s).historical_global_anchor] ∨
  xs = [.digest (common s).historical_global_anchor,.late (common s).lane_transition NBN_LateResult.zero] ∨
  xs = [.digest (common s).historical_global_anchor,.late (common s).lane_transition NBN_LateResult.zero,.payment s]
def Shape (s : Statement) (xs : List Call) : Prop :=
  xs = [.validate s] ∨
  xs = [.validate s,.digest (common s).historical_global_anchor] ∨
  xs = [.validate s,.digest (common s).historical_global_anchor,.late (common s).lane_transition NBN_LateResult.zero] ∨
  xs = [.validate s,.digest (common s).historical_global_anchor,.late (common s).lane_transition NBN_LateResult.zero,.payment s]

theorem late_shape (s : Statement) (anchor : Array U8 32#usize) :
    LateShape s (lateStep s anchor).2 := by
  unfold lateStep
  dsimp only
  cases h : NBN_LateSummary.run enc (common s).lane_transition NBN_LateResult.zero with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok pair => cases pair with
    | mk status late => cases status with
      | Err e => simp only [h]; exact Or.inl rfl
      | Ok u => simp only [h]; exact Or.inr rfl

theorem anchor_shape (s : Statement) : AnchorShape s (anchorStep s).2 := by
  unfold anchorStep
  dsimp only
  cases h : enc (common s).historical_global_anchor with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok anchor =>
    simp only [h]
    rcases late_shape s anchor with one | two
    · rw [one]; exact Or.inr (Or.inl rfl)
    · rw [two]; exact Or.inr (Or.inr rfl)

theorem shape (s : Statement) : Shape s (run s).2 := by
  unfold run
  dsimp only
  cases h : NED_ExecutionComposition.validatorReference s with
  | fail e => simp only [h]; exact Or.inl rfl
  | div => simp only [h]; exact Or.inl rfl
  | ok status => cases status with
    | Err e => simp only [h]; exact Or.inl rfl
    | Ok u =>
      simp only [h]
      rcases anchor_shape s with one | two | three
      · rw [one]; exact Or.inr (Or.inl rfl)
      · rw [two]; exact Or.inr (Or.inr (Or.inl rfl))
      · rw [three]; exact Or.inr (Or.inr (Or.inr rfl))

theorem validation_same (s arg : Statement)
    (reached : Call.validate arg ∈ (run s).2) : arg = s := by
  rcases shape s with one | two | three | four <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.validate.injEq]

theorem payment_same (s arg : Statement)
    (reached : Call.payment arg ∈ (run s).2) : arg = s := by
  rcases shape s with one | two | three | four <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.payment.injEq]

theorem digest_same (s : Statement) (arg : Array U32 8#usize)
    (reached : Call.digest arg ∈ (run s).2) : arg = (common s).historical_global_anchor := by
  rcases shape s with one | two | three | four <;>
    simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.digest.injEq]

theorem late_domain (s : Statement) (arg : NBN_LateSummary.Statement) (out : Slice U8)
    (reached : Call.late arg out ∈ (run s).2) :
    arg = (common s).lane_transition ∧ out = NBN_LateResult.zero ∧ out.length = 1520 := by
  have same : arg = (common s).lane_transition ∧ out = NBN_LateResult.zero := by
    rcases shape s with one | two | three | four <;>
      simp_all only [List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,Call.late.injEq,and_self]
  obtain ⟨rfl,rfl⟩ := same
  refine ⟨rfl,rfl,?_⟩
  simp only [NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
  rfl

#print axioms late_shape
#print axioms anchor_shape
#print axioms shape
#print axioms validation_same
#print axioms payment_same
#print axioms digest_same
#print axioms late_domain
end NED_EncoderCallDomains
