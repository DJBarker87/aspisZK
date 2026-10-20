import PowersP6GeneratedErasureV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersP6GeneratedTotalV1
open AspisR1FromFnP6 AspisR1FromFnP6Generated
open AspisR1PowersConcreteMul AspisR1S3PowersCanonicalTraceV1
open AspisR1PowersP6ClaimAgreementV1 AspisR1PowersP6GeneratedErasureV1

theorem generated_trace_lifts {N : Usize}
    (callback : core.ops.function.FnMut (PowerState N) Usize CallbackWide)
    (hcallback : ∀ state i, callback.call_mut state i=powerFnMutCall state i)
    {count start : Nat} {initial final : PowerState N} {values : List CallbackWide}
    (ht : StatefulFromFnTrace powerStep count start initial values final) :
    ∀ cursor : Usize, cursor.val=start → start+count ≤ Usize.max →
    ∃ finalCursor, StatefulFromFnTrace (fnMutStep callback) count start
      (initial,cursor) values (final,finalCursor) := by
  induction ht with
  | done start state =>
    intro cursor hc hb
    exact ⟨cursor,.done start (state,cursor)⟩
  | @call count start state state' final value values hcall htail ih =>
    intro cursor hc hb
    have hone : (1#usize).val=1 := by decide
    obtain ⟨cursor',hnext,hval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := cursor) (y := 1#usize) (by rw [hone]; omega))
    have hc' : cursor'.val=start+1 := by rw [hone] at hval; omega
    have hoperation : callback.call_mut state cursor=powerStep state start := by
      rw [hcallback,generatedFnMut_eq_callOnce]
      unfold powerStep
      exact AspisR1CurrentPowers.call_once_index_independent
        AspisR1PowersConcreteMul.sourceMul state cursor 0#usize
    have hgen : fnMutStep callback (state,cursor) start=ok (value,(state',cursor')) := by
      simp only [fnMutStep,hoperation,hcall,bind_tc_ok,hnext]
      rfl
    obtain ⟨finalCursor,htrace⟩ := ih cursor' hc' (by omega)
    exact ⟨finalCursor,.call hgen htrace⟩

/-- The generated interface has no cursor overflow for an N-element array:
the final increment reaches N, which is itself a Usize. -/
theorem sourceArrayPowers_total (N : Usize)
    (x : AspisR1CurrentPreparedClaim.Concrete.E)
    (hx : AspisR1CurrentPreparedClaim.Concrete.Canonical x) :
    ∃ out, sourceArrayPowers N x=ok out := by
  have hx' : Canonical (fromClaim x) := hx
  obtain ⟨values,final,hrun,hlen,hall,hfinal⟩ :=
    powersN_model_total (N := N) (fromClaim x) hx'
  have ht := (statefulFromFnRun_success_iff_trace powerStep N.val 0
    (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x) values final).mp hrun
  have hb : 0+N.val ≤ Usize.max := by scalar_tac
  obtain ⟨cursor,htrace⟩ := generated_trace_lifts (sourcePowerCallback N)
    (fun _ _ => rfl) ht 0#usize rfl hb
  have hr := (statefulFromFnRun_success_iff_trace
    (fnMutStep (sourcePowerCallback N)) N.val 0
    ((AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x),0#usize)
    values (final,cursor)).mpr htrace
  let arr : Array CallbackWide N := ⟨values,hlen⟩
  have ha : core.array.from_fn_model N (sourcePowerCallback N)
      (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x)=ok (arr,(final,cursor)) := by
    simp only [core.array.from_fn_model,core.array.from_fn_trace_model,hr,
      packArrayState,dif_pos hlen]
    rfl
  refine ⟨mapClaimArray arr,?_⟩
  simp only [sourceArrayPowers,ha,bind_tc_ok]
  rfl

theorem sourceArrayPowers_eq_claimPowers (N : Usize)
    (x : AspisR1CurrentPreparedClaim.Concrete.E)
    (hx : AspisR1CurrentPreparedClaim.Concrete.Canonical x) :
    sourceArrayPowers N x=AspisR1CurrentPreparedClaim.ClaimPowers.powers N x := by
  obtain ⟨out,hout⟩ := sourceArrayPowers_total N x hx
  exact hout.trans (sourceArrayPowers_success_claim x hx out hout).symm

/-- Full result equality now follows, rather than only successful-output
inclusion: generated array powers is total on canonical inputs. -/
theorem prepared_claim_sourceArray_eq {D H : Type}
    (ops : AspisR1CurrentPreparedClaim.ClaimDotOps D)
    (inst : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
    (sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : AspisR1CurrentPreparedClaim.Concrete.E)
    (g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize)
    (kappa : AspisR1CurrentPreparedClaim.Concrete.E)
    (hk : AspisR1CurrentPreparedClaim.Concrete.Canonical kappa) :
    AspisR1CurrentPreparedClaim.verifier.prepared_claim
      (withSourceArrayPowers ops) inst sem y1 inactive g kappa =
    AspisR1CurrentPreparedClaim.verifier.prepared_claim
      (AspisR1CurrentPreparedClaim.ClaimPowers.withConcretePowers ops)
      inst sem y1 inactive g kappa := by
  unfold AspisR1CurrentPreparedClaim.verifier.prepared_claim
  change (do let k ← sourceArrayPowers 7#usize kappa; _) =
    (do let k ← AspisR1CurrentPreparedClaim.ClaimPowers.powers 7#usize kappa; _)
  rw [sourceArrayPowers_eq_claimPowers 7#usize kappa hk]
  congr 1

#print axioms prepared_claim_sourceArray_eq

#print axioms generated_trace_lifts
#print axioms sourceArrayPowers_total
#print axioms sourceArrayPowers_eq_claimPowers
end AspisR1PowersP6GeneratedTotalV1
