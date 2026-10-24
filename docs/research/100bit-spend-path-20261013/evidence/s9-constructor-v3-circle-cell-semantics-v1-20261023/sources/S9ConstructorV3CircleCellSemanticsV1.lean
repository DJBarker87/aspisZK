import S9ConstructorV3DoubleSemanticsV1
import S9ConstructorV3Loop2InnerCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3CircleCellSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1

/-- The actual continuing circle-factor body writes its same-run values
[ONE,x,T2(x),x*T2(x)] and carries T2(T2(x)). Its exact mutation and
iterator progress are retained as source witnesses. -/
theorem circle_cell_body_success_semantics
    (k : Usize) (iter iterNext : R) (factors factorsOut : Factors)
    (x xNext : Q) (hx : Can x)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.cont (iterNext,factorsOut,xNext))) :
    ∃ (d : Usize) (y q : Q) (i : Usize) (old : Row)
      (back : Row → Factors) (rowOut : Row),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some d,iterNext) ∧
      lift (Std.Usize.wrapping_add 3#usize k) = .ok i ∧
      Array.index_mut_usize factors i = .ok (old,back) ∧
      Array.update old d (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,x,y,q] : Cell) = .ok rowOut ∧
      factorsOut = back rowOut ∧ Can y ∧ Can q ∧ Can xNext ∧
      decode y = decode x*decode x+decode x*decode x-1 ∧
      decode q = decode x*decode y ∧
      decode xNext = decode y*decode y+decode y*decode y-1 := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  obtain ⟨next,hnext,hbody⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors × Q) Factors) =
      ok (ControlFlow.cont (iterNext,factorsOut,xNext) : ControlFlow (R × Factors × Q) Factors) at hbody
    cases hbody
  | some d =>
    obtain ⟨y,hy,hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨q,hq,hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i,hi,hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨mutPair,hmut,hbody⟩ := bind_success_inv _ _ _ hbody
    rcases mutPair with ⟨old,back⟩
    change (do
      let rowOut ← Array.update old d (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,x,y,q] : Cell)
      let xn ← AspisR1S9ActualWeightsNewBoxNewV3.double y
      ok (ControlFlow.cont (iter1,back rowOut,xn) : ControlFlow (R × Factors × Q) Factors)) =
      ok (ControlFlow.cont (iterNext,factorsOut,xNext) : ControlFlow (R × Factors × Q) Factors) at hbody
    obtain ⟨rowOut,hrow,hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨xn,hxn,hbody⟩ := bind_success_inv _ _ _ hbody
    have hs := ControlFlow.cont.inj (Result.ok.inj hbody)
    have hiter : iter1 = iterNext := congrArg Prod.fst hs
    have hfactor : back rowOut = factorsOut := congrArg (fun s : R × Factors × Q => s.2.1) hs
    have hxnext : xn = xNext := congrArg (fun s : R × Factors × Q => s.2.2) hs
    subst iterNext
    subst xn
    obtain ⟨hyc,hyd⟩ := AspisR1S9ConstructorV3DoubleSemanticsV1.generated_double_success_exact x y hx hy
    obtain ⟨hqc,hqd⟩ := generated_mul_success_exact x y q hx hyc hq
    obtain ⟨hxc,hxd⟩ := AspisR1S9ConstructorV3DoubleSemanticsV1.generated_double_success_exact y xNext hyc hxn
    exact ⟨d,y,q,i,old,back,rowOut,hnext,hi,hmut,hrow,hfactor.symm,
      hyc,hqc,hxc,hyd,hqd,hxd⟩

#print axioms circle_cell_body_success_semantics
end AspisR1S9ConstructorV3CircleCellSemanticsV1
