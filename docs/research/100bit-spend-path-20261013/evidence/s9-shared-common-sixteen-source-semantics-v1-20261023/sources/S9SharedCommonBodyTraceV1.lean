import AspisR1S9ProductionPairCutV1.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9SharedCommonBodyTraceV1
abbrev Q := aspis_core.field.QM31
abbrev Common := Array Q 16#usize
abbrev Row := Array (Array Q 4#usize) 5#usize
abbrev R := core.ops.range.Range Usize
abbrev State := R × Common
abbrev Output := weights.Weights × Common
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Exact source control/read/multiply/write events; no field meaning assumed. -/
theorem actual_body_success_trace (self : weights.Weights) (iter : R) (common : Common)
    (out : ControlFlow State Output)
    (h : weights.Weights.pair_loop1.body self iter common=.ok out) :
    (∃ iterNext, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=
      .ok (none,iterNext) ∧ out=.done (self,common)) ∨
    (∃ (j : Usize) (iterNext : R) (row : Row) (cell2 cell3 : Array Q 4#usize)
      (q2 q3 product : Q) (commonNext : Common),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,iterNext) ∧
      Array.index_usize self.factors 0#usize=.ok row ∧
      Array.index_usize row 2#usize=.ok cell2 ∧
      Array.index_usize cell2 (j &&& 3#usize)=.ok q2 ∧
      Array.index_usize row 3#usize=.ok cell3 ∧
      Array.index_usize cell3 (Usize.wrapping_shr j 2#u32)=.ok q3 ∧
      aspis_core.field.QM31.mul q2 q3=.ok product ∧
      Array.update common j product=.ok commonNext ∧ out=.cont (iterNext,commonNext)) := by
  unfold weights.Weights.pair_loop1.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨opt,iterNext⟩
  cases opt with
  | none =>
    exact Or.inl ⟨iterNext,hn,(Result.ok.inj h).symm⟩
  | some j =>
    obtain ⟨lo,hlo,h⟩ := bind_success _ _ _ h
    obtain ⟨row,hr,h⟩ := bind_success _ _ _ h
    obtain ⟨cell2,hc2,h⟩ := bind_success _ _ _ h
    obtain ⟨q2,hq2,h⟩ := bind_success _ _ _ h
    obtain ⟨hi,hhi,h⟩ := bind_success _ _ _ h
    obtain ⟨cell3,hc3,h⟩ := bind_success _ _ _ h
    obtain ⟨q3,hq3,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨commonNext,hu,h⟩ := bind_success _ _ _ h
    have elo : lo=(j &&& 3#usize) := (Result.ok.inj hlo).symm
    have ehi : hi=Usize.wrapping_shr j 2#u32 := (Result.ok.inj hhi).symm
    rw [elo] at hq2
    rw [ehi] at hq3
    exact Or.inr ⟨j,iterNext,row,cell2,cell3,q2,q3,product,commonNext,
      hn,hr,hc2,hq2,hc3,hq3,hm,hu,(Result.ok.inj h).symm⟩

#print axioms actual_body_success_trace
end AspisR1S9SharedCommonBodyTraceV1
