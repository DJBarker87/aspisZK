import CurrentWideCanonicalInjectivityV1
import PowersP6IndexedOutputV1
import CurrentClaimPowersInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersP6ClaimAgreementV1
open AspisR1PowersConcreteMul AspisR1PowersExactProduct
open AspisR1FromFnP6 AspisR1S3PowersCanonicalTraceV1
open AspisR1PowersP6IndexedOutputV1 AspisR1CurrentWideCanonicalInjectivityV1
local notation "ClaimE" => AspisR1CurrentPreparedClaim.Concrete.E

def fromClaim (x : ClaimE) : CallbackWide :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def toClaim (x : CallbackWide) : ClaimE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem to_from_claim (x : ClaimE) : toClaim (fromClaim x)=x := rfl
theorem decode_fromClaim (x : ClaimE) : decode (fromClaim x)=
    AspisR1CurrentPreparedClaim.Concrete.decode x := rfl
theorem canonical_fromClaim (x : ClaimE) : Canonical (fromClaim x) ↔
    AspisR1CurrentPreparedClaim.Concrete.Canonical x := Iff.rfl

/-- The unchanged callback/P6 constructor returns exactly the same raw powers
as the existing proved early-loop claim backend on canonical inputs. -/
theorem source_model_run_agrees_with_claim_powers {N : Usize}
    (x : ClaimE) (hx : AspisR1CurrentPreparedClaim.Concrete.Canonical x)
    (values : List CallbackWide) (final : PowerState N)
    (hrun : statefulFromFnRun powerStep N.val 0
      (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x)=ok (values,final)) :
    ∃ out, AspisR1CurrentPreparedClaim.ClaimPowers.powers N x=ok out ∧
      values.map toClaim=out.val := by
  obtain ⟨out,hout,hexact⟩ :=
    AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact N x hx
  have hx' : Canonical (fromClaim x) := hx
  obtain ⟨hlen,hall,hfinal⟩ := powersN_model_success (fromClaim x) values final hx' hrun
  refine ⟨out,hout,?_⟩
  apply List.ext_getElem
  · simp only [List.length_map,hlen,out.property]
  · intro index hleft hright
    have hi : index<N.val := by simpa only [out.property] using hright
    obtain ⟨actual,hread,hcan,hdecode⟩ :=
      powersN_model_success_indexed (fromClaim x) values final hx' hrun index hi
    have hbound : index<values.length := by omega
    have hactual : values[index]'hbound=actual :=
      Option.some.inj ((List.getElem?_eq_getElem hbound).symm.trans hread)
    obtain ⟨hrefcan,hrefdecode⟩ := hexact ⟨index,hi⟩
    have hreference : Canonical (fromClaim (out.val[index]'hright)) := hrefcan
    have hdecoded : decode actual=decode (fromClaim (out.val[index]'hright)) := by
      rw [decode_fromClaim,hrefdecode]
      simpa only [decode_fromClaim] using hdecode
    have he := (canonical_callback_decode_eq_iff actual
      (fromClaim (out.val[index]'hright)) hcan hreference).mp hdecoded
    simpa only [List.getElem_map,hactual,to_from_claim] using congrArg toClaim he

def sourceModelPowers (N : Usize) (x : ClaimE) : Result (Array ClaimE N) :=
  Bind.bind (statefulFromFnRun powerStep N.val 0
    (AspisR1CurrentPowers.field.WideExact.ONE,fromClaim x)) fun result =>
  if hlen : result.1.length=N.val then
    ok ⟨result.1.map toClaim,by simpa only [List.length_map] using hlen⟩
  else fail .panic

/-- On canonical inputs, the source-callback P6 constructor can replace the
existing claim-powers implementation with exactly the same returned array. -/
theorem sourceModelPowers_eq_claimPowers (N : Usize) (x : ClaimE)
    (hx : AspisR1CurrentPreparedClaim.Concrete.Canonical x) :
    sourceModelPowers N x=AspisR1CurrentPreparedClaim.ClaimPowers.powers N x := by
  have hx' : Canonical (fromClaim x) := hx
  obtain ⟨values,final,hrun,hlen,hexact,hfinal⟩ :=
    powersN_model_total_indexed (N := N) (fromClaim x) hx'
  obtain ⟨out,hout,hvalues⟩ := source_model_run_agrees_with_claim_powers x hx values final hrun
  simp only [sourceModelPowers,hrun,bind_tc_ok,dif_pos hlen,hout]
  apply congrArg Result.ok
  apply Subtype.ext
  exact hvalues

#print axioms sourceModelPowers_eq_claimPowers
#print axioms to_from_claim
#print axioms decode_fromClaim
#print axioms canonical_fromClaim
#print axioms source_model_run_agrees_with_claim_powers
end AspisR1PowersP6ClaimAgreementV1
