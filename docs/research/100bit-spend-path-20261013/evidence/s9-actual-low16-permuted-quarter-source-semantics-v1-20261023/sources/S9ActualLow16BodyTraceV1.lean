import AspisR1S9ProductionPairCutV1.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualLow16BodyTraceV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Powers := Array W 4#usize
abbrev Low := Array W 16#usize
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × Low
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Shared and unshared source low producers have identical bodies, including
PERM and QUARTER². This is full Result equality, not a plain-product model. -/
theorem shared_low_eq (iter : Iter) (ap0 ap1 : Powers) (low : Low) :
    weights.Weights.pair_loop7 iter ap0 ap1 low=weights.Weights.pair_loop15 iter ap0 ap1 low := rfl

theorem low_body_success_trace (ap0 ap1 : Powers) (iter : Iter) (low : Low)
    (out : ControlFlow State Low)
    (h : weights.Weights.pair_loop15.body ap0 ap1 iter low=.ok out) :
    (∃ it,core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (none,it) ∧ out=.done low) ∨
    (∃ (s : Usize) (it : Iter) (lo pi hi pj : Usize) (x y product value : W)
      (m : U32) (lowNext : Low),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some s,it) ∧
      (s % 4#usize : Result Usize)=.ok lo ∧ Array.index_usize weights.PERM lo=.ok pi ∧
      Array.index_usize ap0 pi=.ok x ∧
      (s / 4#usize : Result Usize)=.ok hi ∧ Array.index_usize weights.PERM hi=.ok pj ∧
      Array.index_usize ap1 pj=.ok y ∧
      aspis_core.field.wide_exact.WideExact.mul x y=.ok product ∧
      aspis_core.field.M31.mul weights.QUARTER weights.QUARTER=.ok m ∧
      aspis_core.field.wide_exact.WideExact.mul_m31 product m=.ok value ∧
      Array.update low s value=.ok lowNext ∧ out=.cont (it,lowNext)) := by
  unfold weights.Weights.pair_loop15.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,it⟩
  cases o with
  | none => exact Or.inl ⟨it,hn,(Result.ok.inj h).symm⟩
  | some s =>
    obtain ⟨lo,hl,h⟩ := bind_success _ _ _ h
    obtain ⟨pi,hpi,h⟩ := bind_success _ _ _ h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    obtain ⟨hi,hh,h⟩ := bind_success _ _ _ h
    obtain ⟨pj,hpj,h⟩ := bind_success _ _ _ h
    obtain ⟨y,hy,h⟩ := bind_success _ _ _ h
    obtain ⟨product,hprod,h⟩ := bind_success _ _ _ h
    obtain ⟨m,hm,h⟩ := bind_success _ _ _ h
    obtain ⟨value,hvalue,h⟩ := bind_success _ _ _ h
    obtain ⟨lowNext,hu,h⟩ := bind_success _ _ _ h
    exact Or.inr ⟨s,it,lo,pi,hi,pj,x,y,product,value,m,lowNext,
      hn,hl,hpi,hx,hh,hpj,hy,hprod,hm,hvalue,hu,(Result.ok.inj h).symm⟩

#print axioms shared_low_eq
#print axioms low_body_success_trace
end AspisR1S9ActualLow16BodyTraceV1
