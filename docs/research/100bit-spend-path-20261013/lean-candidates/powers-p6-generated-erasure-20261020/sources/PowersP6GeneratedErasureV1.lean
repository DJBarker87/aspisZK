import PowersP6ClaimAgreementV1
import S4FromFnP6GeneratedInterface
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersP6GeneratedErasureV1
open AspisR1FromFnP6 AspisR1FromFnP6Generated
open AspisR1PowersConcreteMul AspisR1S3PowersCanonicalTraceV1
open AspisR1PowersP6ClaimAgreementV1

theorem generated_step_projects {N : Usize}
    (callback : core.ops.function.FnMut (PowerState N) Usize CallbackWide)
    (hcallback : ∀ state i, callback.call_mut state i=powerFnMutCall state i)
    (state next : PowerState N × Usize) (index : Nat) (value : CallbackWide)
    (hstep : fnMutStep callback state index=ok (value,next)) :
    powerStep state.1 index=ok (value,next.1) := by
  unfold fnMutStep at hstep
  rw [hcallback] at hstep
  cases hc : powerFnMutCall state.1 state.2 with
  | fail e => simp only [hc,bind_tc_fail] at hstep; cases hstep
  | div => simp only [hc,bind_tc_div] at hstep; cases hstep
  | ok pair =>
    rcases pair with ⟨actual,closure⟩
    simp only [hc,bind_tc_ok] at hstep
    cases hi : state.2 + 1#usize with
    | fail e => simp only [hi,bind_tc_fail] at hstep; cases hstep
    | div => simp only [hi,bind_tc_div] at hstep; cases hstep
    | ok cursor =>
      simp only [hi,bind_tc_ok] at hstep
      have hp := Result.ok.inj hstep
      have hv : actual=value := congrArg Prod.fst hp
      have hs : closure=next.1 := congrArg (fun p => p.2.1) hp
      rw [← hv,← hs]
      unfold powerStep
      rw [generatedFnMut_eq_callOnce] at hc
      exact (AspisR1CurrentPowers.call_once_index_independent
        AspisR1PowersConcreteMul.sourceMul state.1 0#usize state.2).trans hc

theorem generated_trace_projects {N : Usize}
    (callback : core.ops.function.FnMut (PowerState N) Usize CallbackWide)
    (hcallback : ∀ state i, callback.call_mut state i=powerFnMutCall state i)
    {count start : Nat} {initial final : PowerState N × Usize}
    {values : List CallbackWide}
    (ht : StatefulFromFnTrace (fnMutStep callback) count start initial values final) :
    StatefulFromFnTrace powerStep count start initial.1 values final.1 := by
  induction ht with
  | done start state => exact .done start state.1
  | @call count start state state' final value values hcall htail ih =>
    exact .call (generated_step_projects callback hcallback state state' start value hcall) ih

theorem generated_array_success_claim_powers {N : Usize}
    (callback : core.ops.function.FnMut (PowerState N) Usize CallbackWide)
    (hcallback : ∀ state i, callback.call_mut state i=powerFnMutCall state i)
    (x : AspisR1CurrentPreparedClaim.Concrete.E)
    (hx : AspisR1CurrentPreparedClaim.Concrete.Canonical x)
    (values : Array CallbackWide N) (final : PowerState N × Usize)
    (harray : core.array.from_fn_model N callback
      (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x)=ok (values,final)) :
    ∃ out, AspisR1CurrentPreparedClaim.ClaimPowers.powers N x=ok out ∧
      values.val.map toClaim=out.val := by
  have ht := core_array_from_fn_model_success_trace N callback
    (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x) harray
  have hp := generated_trace_projects callback hcallback ht
  have hr := (statefulFromFnRun_success_iff_trace powerStep N.val 0
    (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x) values.val final.1).mpr hp
  exact source_model_run_agrees_with_claim_powers x hx values.val final.1 hr

/-- The operation record used by the reviewed library interface. Its call_mut
is precisely the checked source FnMut/back-state operation. FnOnceInst is
required by the interface but never invoked by from_fn_model. -/
def sourcePowerCallback (N : Usize) :
    core.ops.function.FnMut (PowerState N) Usize CallbackWide := {
  FnOnceInst := {call_once := fun state i => do
    let (value, _) ← powerFnMutCall state i
    ok value}
  call_mut := powerFnMutCall
}

def mapClaimArray {N : Usize} (values : Array CallbackWide N) :
    Array AspisR1CurrentPreparedClaim.Concrete.E N :=
  ⟨values.val.map toClaim,by simpa only [List.length_map] using values.property⟩

def sourceArrayPowers (N : Usize) (x : AspisR1CurrentPreparedClaim.Concrete.E) :
    Result (Array AspisR1CurrentPreparedClaim.Concrete.E N) := do
  let (values, _) ← core.array.from_fn_model N (sourcePowerCallback N)
    (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x)
  ok (mapClaimArray values)

/-- Successful array-interface source powers returns exactly the already
proved claim powers result. No callback law, trace, or raw-output equality
premise remains; the reviewed library model itself is still P6. -/
theorem sourceArrayPowers_success_claim {N : Usize}
    (x : AspisR1CurrentPreparedClaim.Concrete.E)
    (hx : AspisR1CurrentPreparedClaim.Concrete.Canonical x)
    (out : Array AspisR1CurrentPreparedClaim.Concrete.E N)
    (h : sourceArrayPowers N x=ok out) :
    AspisR1CurrentPreparedClaim.ClaimPowers.powers N x=ok out := by
  unfold sourceArrayPowers at h
  cases ha : core.array.from_fn_model N (sourcePowerCallback N)
      (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x) with
  | fail e => simp only [ha,bind_tc_fail] at h; cases h
  | div => simp only [ha,bind_tc_div] at h; cases h
  | ok pair =>
    rcases pair with ⟨values,final⟩
    simp only [ha,bind_tc_ok] at h
    have hout : mapClaimArray values=out := Result.ok.inj h
    obtain ⟨reference,hreference,hvalues⟩ := generated_array_success_claim_powers
      (sourcePowerCallback N) (fun _ _ => rfl) x hx values final ha
    have heq : out=reference := by
      apply Subtype.ext
      exact (congrArg Subtype.val hout).symm.trans hvalues
    rw [heq]
    exact hreference

def withSourceArrayPowers {D : Type}
    (ops : AspisR1CurrentPreparedClaim.ClaimDotOps D) :
    AspisR1CurrentPreparedClaim.ClaimDotOps D :=
  {ops with powers := sourceArrayPowers}

/-- The array-interface caller has no successful output unavailable to the
existing concrete claim caller on canonical kappa. This is the direction
needed to reuse soundness; no library totality premise is needed. -/
theorem prepared_claim_sourceArray_success {D H : Type}
    (ops : AspisR1CurrentPreparedClaim.ClaimDotOps D)
    (inst : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
    (sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : AspisR1CurrentPreparedClaim.Concrete.E)
    (g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize)
    (kappa : AspisR1CurrentPreparedClaim.Concrete.E)
    (out : core.result.Result
      AspisR1CurrentPreparedClaim.Concrete.E AspisR1CurrentPreparedClaim.verifier.Error)
    (hk : AspisR1CurrentPreparedClaim.Concrete.Canonical kappa)
    (h : AspisR1CurrentPreparedClaim.verifier.prepared_claim
      (withSourceArrayPowers ops) inst sem y1 inactive g kappa=ok out) :
    AspisR1CurrentPreparedClaim.verifier.prepared_claim
      (AspisR1CurrentPreparedClaim.ClaimPowers.withConcretePowers ops)
      inst sem y1 inactive g kappa=ok out := by
  unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim at h ⊢
  change (do let k ← sourceArrayPowers 7#usize kappa; _)=ok out at h
  obtain ⟨k,hpowers,htail⟩ := result_bind_ok_inv _ _ h
  have hp := sourceArrayPowers_success_claim kappa hk k hpowers
  change (do let k ← AspisR1CurrentPreparedClaim.ClaimPowers.powers 7#usize kappa; _)=ok out
  rw [hp,bind_tc_ok]
  exact htail

#print axioms prepared_claim_sourceArray_success

#print axioms sourceArrayPowers_success_claim

#print axioms generated_step_projects
#print axioms generated_trace_projects
#print axioms generated_array_success_claim_powers
end AspisR1PowersP6GeneratedErasureV1
