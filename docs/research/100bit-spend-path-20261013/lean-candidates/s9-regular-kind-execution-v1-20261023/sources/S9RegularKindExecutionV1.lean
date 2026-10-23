import S9ActualProcessKindTensorReachedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9RegularKindExecutionV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev Dot := fast_pairing.EbyKDot

/-- All events of ONE actual inlined regular driver. This is an OUTPUT
witness built from its accepted call, not an assumed implementation contract. -/
structure Execution (self : weights.Weights) (kind : Usize) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts) where
  input : Slice Q
  back : Slice Q → Scratch
  tensorOut : Slice Q
  factorRow : Array (Array Q 4#usize) 5#usize
  f0 : Array Q 4#usize
  f1 : Array Q 4#usize
  scale0 : W
  scale1 : W
  scale : W
  initialDot : Dot
  finalDot : Dot
  dotValue : W
  storedValue : W
  borrow : alloc.vec.Vec.deref_mut scratch=(input,back)
  tensor : weights.Weights.tensor self (rowOfKind kind) 2#usize input=.ok tensorOut
  factors : Array.index_usize self.factors (rowOfKind kind)=.ok factorRow
  factor0 : Array.index_usize factorRow 0#usize=.ok f0
  scalar0 : weights.Weights.scalar_factor f0 ap0=.ok scale0
  factor1 : Array.index_usize factorRow 1#usize=.ok f1
  scalar1 : weights.Weights.scalar_factor f1 ap1=.ok scale1
  scaled : aspis_core.field.wide_exact.WideExact.mul scale0 scale1=.ok scale
  scratchBack : scratchOut=back tensorOut
  newDot : fast_pairing.EbyKDot.new=.ok initialDot
  pushes : weights.push_byte_products initialDot f (alloc.vec.Vec.deref scratchOut) n=
    .ok (.Ok (),finalDot)
  finish : fast_pairing.EbyKDot.finish finalDot=.ok dotValue
  product : aspis_core.field.wide_exact.WideExact.mul scale dotValue=.ok storedValue
  write : Array.update parts kind storedValue=.ok partsOut

private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Accepted actual S2/two-fold regular process_kind supplies its OWN tensor,
borrow/back, both scalar factors, initial zero constructor, complete push run,
SAME final finish, scale multiplication and actual returned parts update.
No tensor/weights meaning, child success, field Can or finish is a premise. -/
theorem process_kind_success_execution
    (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (hcall : weights.process_kind self kind alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) :
    Nonempty (Execution self kind f n ap0 ap1 scratch scratchOut parts partsOut) := by
  have hnotD : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.D=.ok false := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  unfold weights.process_kind at hcall
  rw [hnotD] at hcall
  simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte] at hcall
  obtain ⟨row,hrow,hcall⟩ := bind_success _ _ _ hcall
  have hrowCall : (if kind < 4#usize then Result.ok (Usize.wrapping_sub kind 1#usize)
      else Result.ok (Usize.wrapping_sub kind 2#usize))=.ok (rowOfKind kind) := by
    unfold rowOfKind
    split <;> rfl
  have hrowEq : row=rowOfKind kind := (Result.ok.inj (hrowCall.symm.trans hrow)).symm
  subst row
  obtain ⟨borrow,hborrow,hcall⟩ := bind_success _ _ _ hcall
  rcases borrow with ⟨input,back⟩
  have hb : alloc.vec.Vec.deref_mut scratch=(input,back) := Result.ok.inj hborrow
  obtain ⟨tensorOut,htensor,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨factorRow,hfactorRow,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨f0,hf0,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨scale0,hscale0,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨scalePair,hscalePair,hcall⟩ := bind_success _ _ _ hcall
  rcases scalePair with ⟨scratch1,scaleFinal⟩
  obtain ⟨f1,hf1,hscalePair⟩ := bind_success _ _ _ hscalePair
  obtain ⟨scale1,hscale1,hscalePair⟩ := bind_success _ _ _ hscalePair
  obtain ⟨scale,hscale,hscalePair⟩ := bind_success _ _ _ hscalePair
  have hback : back tensorOut=scratch1 := congrArg Prod.fst (Result.ok.inj hscalePair)
  have hscaleEq : scale=scaleFinal := congrArg Prod.snd (Result.ok.inj hscalePair)
  subst scaleFinal
  obtain ⟨initialDot,hnew,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨pushed,hpush,hcall⟩ := bind_success _ _ _ hcall
  rcases pushed with ⟨result,finalDot⟩
  cases result with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at hcall
    cases hcall
  | Ok u =>
    cases u
    obtain ⟨cf,hcf,hcall⟩ := bind_success
      (core.result.Result.Insts.CoreOpsTry.branch (E:=verifier.Error) (.Ok ())) _ _ hcall
    have hcfEq : cf=core.ops.control_flow.ControlFlow.Continue () := (Result.ok.inj hcf).symm
    cases hcfEq
    obtain ⟨dotValue,hfinish,hcall⟩ := bind_success _ _ _ hcall
    obtain ⟨storedValue,hproduct,hcall⟩ := bind_success _ _ _ hcall
    obtain ⟨finalParts,hwrite,hcall⟩ := bind_success _ _ _ hcall
    have hs : scratch1=scratchOut := congrArg (fun v => v.2.1) (Result.ok.inj hcall)
    have hp : finalParts=partsOut := congrArg (fun v => v.2.2) (Result.ok.inj hcall)
    have hbackOut : scratchOut=back tensorOut := (hback.trans hs).symm
    subst finalParts
    exact ⟨{
      input := input
      back := back
      tensorOut := tensorOut
      factorRow := factorRow
      f0 := f0
      f1 := f1
      scale0 := scale0
      scale1 := scale1
      scale := scale
      initialDot := initialDot
      finalDot := finalDot
      dotValue := dotValue
      storedValue := storedValue
      borrow := hb
      tensor := htensor
      factors := hfactorRow
      factor0 := hf0
      scalar0 := hscale0
      factor1 := hf1
      scalar1 := hscale1
      scaled := hscale
      scratchBack := hbackOut
      newDot := hnew
      pushes := by simpa only [hs] using hpush
      finish := hfinish
      product := hproduct
      write := hwrite }⟩

#print axioms process_kind_success_execution
end AspisR1S9RegularKindExecutionV1
