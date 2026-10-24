import S9ActualProcessKindTensorReachedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ProcessKindScalarSourceV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- SAME actual S2/folds2 process-kind call yields its real factor0/factor1
reads and BOTH scalar outputs, before its dot/finish/error suffix. -/
theorem process_kind_success_reaches_scalars
    (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch)
    (parts partsOut : Parts) (result : Outcome)
    (hs2 : self.variant=transport.Variant.S2)
    (hcall : weights.process_kind self kind alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (result,scratchOut,partsOut)) :
    ∃ (row : Array (Array Q 4#usize) 5#usize) (f0 f1 : Array Q 4#usize)
      (scale0 scale1 scaleProduct : W),
      Array.index_usize self.factors (rowOfKind kind)=.ok row ∧
      Array.index_usize row 0#usize=.ok f0 ∧
      weights.Weights.scalar_factor f0 ap0=.ok scale0 ∧
      Array.index_usize row 1#usize=.ok f1 ∧
      weights.Weights.scalar_factor f1 ap1=.ok scale1 ∧
      aspis_core.field.wide_exact.WideExact.mul scale0 scale1=.ok scaleProduct := by
  have hnotD : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.D = .ok false := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  unfold weights.process_kind at hcall
  rw [hnotD] at hcall
  simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte] at hcall
  obtain ⟨row,hrow,hcall⟩ := bind_success _ _ _ hcall
  have hrowCall : (if kind < 4#usize then Result.ok (Usize.wrapping_sub kind 1#usize)
      else Result.ok (Usize.wrapping_sub kind 2#usize)) = Result.ok (rowOfKind kind) := by
    unfold rowOfKind
    split <;> rfl
  have hrowEq : row=rowOfKind kind := (Result.ok.inj (hrowCall.symm.trans hrow)).symm
  obtain ⟨pair,hborrow,hcall⟩ := bind_success _ _ _ hcall
  rcases pair with ⟨input,back⟩
  obtain ⟨tensorOut,htensor,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨factorRow,hfactorRow,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨f0,hf0,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨scale0,hscale0,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨pairScale,hpairScale,hcall⟩ := bind_success _ _ _ hcall
  have hscalePack := hpairScale
  simp only [↓reduceIte] at hscalePack
  obtain ⟨f1,hf1,hscalePack⟩ := bind_success _ _ _ hscalePack
  obtain ⟨scale1,hscale1,hscalePack⟩ := bind_success _ _ _ hscalePack
  obtain ⟨scaleProduct,hproduct,hscalePack⟩ := bind_success _ _ _ hscalePack
  refine ⟨factorRow,f0,f1,scale0,scale1,scaleProduct,?_,hf0,hscale0,hf1,hscale1,hproduct⟩
  rw [←hrowEq]
  exact hfactorRow

#print axioms process_kind_success_reaches_scalars
end AspisR1S9ProcessKindScalarSourceV1
