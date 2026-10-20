import SelectedWideViewFunsV1
import PreparedParsedInactiveV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1SelectedWideViewV1

def prepCarrier (x : aspis_core.field.wide_exact.WideExact) : AspisR1ClaimPreparedBridge.PE :=
  { c0 := { c0 := {a:=x.c0.c0.a,b:=x.c0.c0.b},c1:={a:=x.c0.c1.a,b:=x.c0.c1.b} },
    c1 := { c0 := {a:=x.c1.c0.a,b:=x.c1.c0.b},c1:={a:=x.c1.c1.a,b:=x.c1.c1.b} } }

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B}
    {out : B} (h : (do let x ← r; f x)=ok out) :
    ∃ x,r=ok x ∧ f x=ok out := by
  cases r with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem parser_carrier_same (bytes : Slice U8) :
    (do let o ← viewFromBytes bytes;ok (o.map prepCarrier))=
      AspisR1PreparedParsedInactiveV1.parseInactive bytes := by
  unfold viewFromBytes AspisR1PreparedParsedInactiveV1.parseInactive
  cases h : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes with
  | fail e => rfl
  | div => rfl
  | ok o => cases o <;> rfl

theorem wide_view_inactive_parse (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    ∃ bytes, AspisR1PreparedParsedInactiveV1.parseInactive bytes=
      ok (some (prepCarrier out.inactive)) := by
  unfold verifier.candidate.wide_view at h
  obtain ⟨i,hi,h⟩ := bind_ok_inv h
  obtain ⟨i1,hi1,h⟩ := bind_ok_inv h
  obtain ⟨bytes,hbytes,h⟩ := bind_ok_inv h
  obtain ⟨parsed,hparsed,h⟩ := bind_ok_inv h
  cases parsed with
  | none =>
    simp [viewOptionOkOr,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | some x =>
    simp only [viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨i2,hi2,h⟩ := bind_ok_inv h
    obtain ⟨s1,hs1,h⟩ := bind_ok_inv h
    obtain ⟨i3,hi3,h⟩ := bind_ok_inv h
    obtain ⟨s2,hs2,h⟩ := bind_ok_inv h
    obtain ⟨r1,hr1,h⟩ := bind_ok_inv h
    obtain ⟨a,ha,h⟩ := bind_ok_inv h
    obtain ⟨i4,hi4,h⟩ := bind_ok_inv h
    obtain ⟨s3,hs3,h⟩ := bind_ok_inv h
    obtain ⟨i5,hi5,h⟩ := bind_ok_inv h
    obtain ⟨s4,hs4,h⟩ := bind_ok_inv h
    obtain ⟨s5,hs5,h⟩ := bind_ok_inv h
    have hout := core.result.Result.Ok.inj (Result.ok.inj h)
    have hinactive : x=out.inactive := congrArg verifier.View.inactive hout
    refine ⟨bytes,?_⟩
    rw [← parser_carrier_same, hparsed,bind_tc_ok]
    exact congrArg (fun z => ok (some (prepCarrier z))) hinactive

theorem wide_view_inactive_canonical (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    AspisR1CurrentPreparedClaim.Concrete.Canonical
      (AspisR1ClaimPreparedBridge.toClaimE (prepCarrier out.inactive)) := by
  obtain ⟨bytes,hparsed⟩ := wide_view_inactive_parse proof semantic y1 out h
  exact (AspisR1PreparedParsedInactiveV1.parsed_canonical bytes _ hparsed).2

#print axioms parser_carrier_same
#print axioms wide_view_inactive_parse
#print axioms wide_view_inactive_canonical
end AspisR1SelectedWideViewV1
