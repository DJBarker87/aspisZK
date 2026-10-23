import S9CanonicalPartsUpdateV1
import S9ActualPairScalarFactorShortV1
import S9ActualEbyKFinishCanonicalV1
import S9ActualProcessKindTensorReachedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ProcessKindPartsCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9NativeWideDecodedArithmeticV1
open AspisR1S9ActualFinalSumV1
abbrev W := aspis_core.field.wide_exact.WideExact
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
private theorem bind_success {X Y : Type} (m : Result X) (next : X → Result Y) (out : Y)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Canonicality preservation of the same accepted actual S2 kind call. The
actual dot finish supplies its own canonicality even for arbitrary dot state.
Factor-vector canonicality, field-byte canonicality and dot-value meaning are
not hypotheses; power/initial-parts canonicality and kind bounds are explicit. -/
theorem process_kind_success_preserves_good
    (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch)
    (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2) (hkind : kind.val<7)
    (hp0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0)
    (hp1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1)
    (hparts : Good parts)
    (hcall : weights.process_kind self kind alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) : Good partsOut := by
  have hnotD : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.D=.ok false := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  unfold weights.process_kind at hcall
  rw [hnotD] at hcall
  simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte] at hcall
  obtain ⟨row,hrow,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨borrow,hborrow,hcall⟩ := bind_success _ _ _ hcall
  rcases borrow with ⟨input,back⟩
  obtain ⟨tensorOut,htensor,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨factorRow,hfactorRow,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨f0,hf0,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨scale0,hs0,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨scalePair,hscalePair,hcall⟩ := bind_success _ _ _ hcall
  rcases scalePair with ⟨scratch1,scaleFinal⟩
  obtain ⟨f1,hf1,hscalePair⟩ := bind_success _ _ _ hscalePair
  obtain ⟨scale1,hs1,hscalePair⟩ := bind_success _ _ _ hscalePair
  obtain ⟨scaleProduct,hm,hscalePair⟩ := bind_success _ _ _ hscalePair
  have hc0 := (AspisR1S9ActualPairScalarFactorShortV1.actual_scalar_factor_success_maps
    f0 ap0 scale0 hp0 hs0).1
  have hc1 := (AspisR1S9ActualPairScalarFactorShortV1.actual_scalar_factor_success_maps
    f1 ap1 scale1 hp1 hs1).1
  have hcp := (actual_mul_success_decoded scale0 scale1 scaleProduct hc0 hc1 hm).1
  have hscaleEq : scaleProduct=scaleFinal := congrArg Prod.snd (Result.ok.inj hscalePair)
  have hscaleCan : Canonical scaleFinal := hscaleEq ▸ hcp
  obtain ⟨dot,hnew,hcall⟩ := bind_success _ _ _ hcall
  obtain ⟨pushed,hpush,hcall⟩ := bind_success _ _ _ hcall
  rcases pushed with ⟨result,dotOut⟩
  cases result with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at hcall
    cases hcall
  | Ok u =>
    cases u
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at hcall
    obtain ⟨dotValue,hfinish,hcall⟩ := bind_success _ _ _ hcall
    obtain ⟨value,hvalue,hcall⟩ := bind_success _ _ _ hcall
    obtain ⟨finalParts,hupdate,hcall⟩ := bind_success _ _ _ hcall
    have hd := AspisR1S9ActualEbyKFinishCanonicalV1.actual_finish_success_canonical dotOut dotValue hfinish
    have hv := (actual_mul_success_decoded scaleFinal dotValue value hscaleCan hd hvalue).1
    have he : finalParts=partsOut := congrArg (fun v => v.2.2) (Result.ok.inj hcall)
    have hg := AspisR1S9CanonicalPartsUpdateV1.update_preserves_good parts finalParts kind value
      hkind hparts hv hupdate
    exact he ▸ hg

#print axioms process_kind_success_preserves_good
end AspisR1S9ProcessKindPartsCanonicalV1
