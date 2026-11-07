import LIB_VClaimsCanonical
import LIB_VResult
set_option autoImplicit false
noncomputable section
namespace LIB_VClaims
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 ClaimsUnrolledFinish
def parent (p : Prefix) : AspisR1ClaimsUnrolledParent.Claims :=
 Classical.choose (LIB_VClaimsCanonical.pure_canonical p)
theorem parent_exact (p : Prefix) :
 NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref (fromMainPrefix (prefixRaw p)))=
 .ok (.Ok (parent p)) := (Classical.choose_spec (LIB_VClaimsCanonical.pure_canonical p)).1
theorem parent_canonical (p : Prefix) : LIB_VClaimsCanonical.AllRows (parent p) :=
 (Classical.choose_spec (LIB_VClaimsCanonical.pure_canonical p)).2
def value (p : Prefix) : Claims :=
 ⟨(parent p).val.attach.map (fun row=>LIB_VArray.lift (toMainArray row.val)
  (parent_canonical p row.val row.property)),by simpa using (parent p).property⟩
theorem value_raw (p : Prefix) : claimsRaw (value p) = NKA_ClaimsEffects.main (parent p) := by
 apply Subtype.ext
 simp only [claimsRaw,value,LIB_VScalarCarriers.array,List.map_map,Function.comp_def,
  k29Raw,LIB_VArray.raw_lift,NKA_ClaimsEffects.main]
 simp
/-- Exact CLOSED NKA cohort, with arbitrary returning reservation, not a
successful allocator premise. The two arms are projected to Env below. -/
theorem cohort (p : Prefix) (reservation : NP6_StdModel.Reservation) :
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation) (prefixRaw p)=
 toMainStatus (NKA_ClaimsModel.reserveResult reservation (parent p)) := by
 obtain ⟨other,pure,model⟩ := NKA_ClaimsModel.parsed reservation p.source p.parsed p.parse_eq
 have same := core.result.Result.Ok.inj (Result.ok.inj (pure.symm.trans (parent_exact p)))
 subst other
 exact congrArg toMainStatus model
def eval (p : Prefix) (env : RSL.Env) : Except WErr Claims :=
 if env.reservation then .ok (value p) else .error .Allocation
def claims : RSL.Child Prefix (Except WErr Claims) :=
 ⟨fun p=>p.source.val.length≤57607,fun p=>LIB_Carriers.graph (eval p) (fun _=>[])⟩
theorem success_exact (p : Prefix) :
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) (prefixRaw p)=
 .ok (.Ok (claimsRaw (value p))) := by
 rw [cohort,value_raw]
 rfl
theorem error_exact (p : Prefix) (e : NP6_StdModel.ReserveError) :
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Err e)) (prefixRaw p)=.ok (.Err .Allocation) := by
 rw [cohort]
 rfl
theorem returns (p : Prefix) (env : RSL.Env) :
 NND_Returned.Returns (claims.law p) env (eval p env) := LIB_Carriers.graph_returns _ _ env
theorem functional : RSL.Child.Functional claims := fun _ _=>LIB_Carriers.graph_functional _ _
theorem law_exact (p : Prefix) (env : RSL.Env) (o : RSL.Obs (Except WErr Claims)) :
 claims.law p env o ↔ o=⟨.ret (eval p env),[]⟩ := Iff.rfl
#print axioms parent_exact
#print axioms parent_canonical
#print axioms value_raw
#print axioms cohort
#print axioms success_exact
#print axioms error_exact
#print axioms returns
#print axioms functional
#print axioms law_exact
end LIB_VClaims
