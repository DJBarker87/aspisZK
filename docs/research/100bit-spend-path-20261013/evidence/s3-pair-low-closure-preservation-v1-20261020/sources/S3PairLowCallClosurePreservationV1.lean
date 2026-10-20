import S3PairLowCallProjectedStepRootV1

open Aeneas Aeneas.Std Result
open AspisR1FromFnP6 AspisR1FromFnP6Generated
set_option autoImplicit false

namespace AspisR1PairLowCallCut

theorem actual_callback_success_preserves_closure
    (ops : LowFieldOps) (c : weights.s2_twofold_low_array.closure)
    (i : Usize) {v : field.WideExact} {next : weights.s2_twofold_low_array.closure}
    (h : weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops c i = .ok (v,next)) : next = c := by
  rw [call_mut_read_form] at h
  obtain ⟨r,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨p,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨x,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨d,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨q,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨y,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨xy,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨scale,_,h⟩ := result_bind_ok_inv _ _ h
  obtain ⟨out,_,h⟩ := result_bind_ok_inv _ _ h
  exact (congrArg Prod.snd (Result.ok.inj h)).symm

/-- A successful source-shaped from_fn run preserves the exact input
closure whenever its actual callback does. No projection injectivity or
individual callback-success hypotheses are needed. -/
theorem from_fn_model_success_preserves_closure {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T) (initial : F)
    (hcallback : ∀ (c : F) (i : Usize) (v : T) (next : F),
      callback.call_mut c i = .ok (v,next) → next = c)
    {values : Aeneas.Std.Array T N} {final : F × Usize}
    (h : core.array.from_fn_model N callback initial = .ok (values,final)) :
    final.1 = initial := by
  have htrace := core_array_from_fn_model_success_trace N callback initial h
  have hstep : ∀ (state : F × Usize) (i : Nat) (v : T) (next : F × Usize),
      state.1 = initial → fnMutStep callback state i = .ok (v,next) →
      True ∧ next.1 = initial := by
    intro state i v next hinitial hcall
    unfold fnMutStep at hcall
    obtain ⟨pair,hcb,hrest⟩ := result_bind_ok_inv _ _ hcall
    rcases pair with ⟨value,closure⟩
    obtain ⟨cursor,_hcursor,hout⟩ := result_bind_ok_inv _ _ hrest
    have hclosure : closure = next.1 :=
      congrArg (fun x : T × (F × Usize) => x.2.1) (Result.ok.inj hout)
    exact ⟨True.intro,hclosure.symm.trans ((hcallback _ _ _ _ hcb).trans hinitial)⟩
  exact (statefulFromFnTrace_preserves
    (fun state _ => state.1 = initial) (fun _ => True) hstep rfl htrace).2

theorem actual_low_array_success_preserves_closure
    (ops : LowFieldOps) (c : weights.s2_twofold_low_array.closure)
    {values : Aeneas.Std.Array field.WideExact 16#usize}
    {final : weights.s2_twofold_low_array.closure × Usize}
    (h : weights.s2_twofold_low_array_model ops c.1 c.2 = .ok (values,final)) :
    final.1 = c := by
  apply from_fn_model_success_preserves_closure (16#usize)
    (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops) c
    (fun c i v next hcall => actual_callback_success_preserves_closure ops c i hcall)
  cases c
  simpa only [weights.s2_twofold_low_array_model] using h

#print axioms actual_callback_success_preserves_closure
#print axioms from_fn_model_success_preserves_closure
#print axioms actual_low_array_success_preserves_closure
end AspisR1PairLowCallCut
