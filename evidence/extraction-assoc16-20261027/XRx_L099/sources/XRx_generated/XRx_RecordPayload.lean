import XRu_RecordCuts
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRx_RecordPayload
/-- Both validation phases return precisely the SAME actual suffix read.
No alternate accepted record or payload is supplied. -/
theorem source (row : U8) (bytes payload : Slice U8)
 (run : r1_wire.parse_record row bytes=ok (.Ok payload)) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
  bytes {start:=5#usize}=ok payload := by
 unfold r1_wire.parse_record at run
 obtain ⟨o,_,run⟩ := bind_success _ _ _ run
 cases o with
 | none =>
  simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from] at run
 | some pair =>
  rcases pair with ⟨tag,size⟩
  simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
  obtain ⟨full,_,run⟩ := bind_success _ _ _ run
  split at run
  · cases run
  · obtain ⟨actual,_,run⟩ := bind_success _ _ _ run
    split at run
    · cases run
    · iterate 6 obtain ⟨x,_,run⟩ := bind_success _ _ _ run
      split at run
      · cases run
      · obtain ⟨out,read,run⟩ := bind_success _ _ _ run
        split at run
        · obtain ⟨validated,_,run⟩ := bind_success _ _ _ run
          cases validated with
          | Err e =>
           simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
          | Ok unit =>
           cases unit
           have same : out=payload := core.result.Result.Ok.inj (Result.ok.inj run)
           simpa only [same] using read
        · have same : out=payload := core.result.Result.Ok.inj (Result.ok.inj run)
          simpa only [same] using read
#print axioms source
end XRx_RecordPayload
