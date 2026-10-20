import SelectedWideViewInactiveV1
import PreparedInactiveCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1SelectedWideViewInactiveCodecV1
open AspisR1SelectedWideViewV1 AspisR1PreparedParsedInactiveV1
open AspisR1ClaimPreparedBridge AspisR1CurrentPreparedClaim.Concrete

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B}
    {out : B} (h : (do let x ← r; f x)=ok out) :
    ∃ x,r=ok x ∧ f x=ok out := by
  cases r with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem wide_view_inactive_source_slice (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    ∃ lo hi bytes,
      compact.OFF_INACTIVE=ok lo ∧ compact.OFF_ROUND0=ok hi ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=lo, «end»:=hi}=ok bytes ∧
      AspisR1PreparedParsedInactiveV1.parseInactive bytes=
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
    refine ⟨i,i1,bytes,hi,hi1,hbytes,?_⟩
    rw [← parser_carrier_same, hparsed,bind_tc_ok]
    exact congrArg (fun z => ok (some (prepCarrier z))) hinactive


/-- No separate parser, canonicality, or decoded-value premise is needed.
The returned frame is the same slice selected from this successful source View. -/
theorem wide_view_inactive_source_decodes
    (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    ∃ (lo hi : Usize) (bytes : Slice U8) (frame : Array U8 32#usize),
      compact.OFF_INACTIVE=ok lo ∧ compact.OFF_ROUND0=ok hi ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=lo, «end»:=hi}=ok bytes ∧
      frame.val=bytes.val ∧
      AspisR1.FoldedLeafCodec.decodeWide
        (List.ofFn (AspisR1.WideParserArrayHalves.arrayBytes32 frame))=
          some (decode (toClaimE (prepCarrier out.inactive))) := by
  obtain ⟨lo,hi,bytes,hlo,hhi,hbytes,hparse⟩ :=
    wide_view_inactive_source_slice proof semantic y1 out h
  have hlen := (parsed_canonical bytes _ hparse).1
  let frame : Array U8 32#usize := ⟨bytes.val,by
    simpa only [UScalar.ofNatCore_val_eq] using hlen⟩
  have hs : Array.to_slice frame=bytes := by
    apply Subtype.ext
    rfl
  refine ⟨lo,hi,bytes,frame,hlo,hhi,hbytes,rfl,?_⟩
  exact AspisR1PreparedInactiveCodecV1.parsed_inactive_decodes frame _ (by
    rw [hs]
    exact hparse)

#print axioms wide_view_inactive_source_slice
#print axioms wide_view_inactive_source_decodes
end AspisR1SelectedWideViewInactiveCodecV1
