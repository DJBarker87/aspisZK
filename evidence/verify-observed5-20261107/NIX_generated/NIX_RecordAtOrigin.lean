import NIH_RustBind
import NGX_RecordAt
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIX_RecordAtOrigin
open AspisR1PrefixAggregateParser
/-- The original aggregate parser stores this exact passed framed record. -/
theorem result (bytes frame : Slice U8) (row : U8) (offset finish : Usize)
 (run : r1_wire.parse_record_at bytes row offset=ok (.Ok (frame,finish))) :
 ∃ payload,r1_wire.parse_record row frame=ok (.Ok payload) := by
 rw [NGX_RecordAt.source] at run
 unfold NGX_RecordAt.computation at run
 obtain ⟨shape,_,tail⟩:=FIv_Map.bind_success _ _ _ run
 obtain ⟨pair,_,tail⟩:=FIv_Map.bind_success _ _ _ tail
 rcases pair with ⟨tag,size⟩
 change ((5#usize+size : Result Usize) >>= _) =
   (ok (core.result.Result.Ok (frame,finish)) :
    Result (core.result.Result (Slice U8×Usize) r1_wire.Error)) at tail
 obtain ⟨length,_,tail⟩:=FIv_Map.bind_success _ _ _ tail
 obtain ⟨next,_,tail⟩:=FIv_Map.bind_success _ _ _ tail
 obtain ⟨candidate,_,tail⟩:=FIv_Map.bind_success _ _ _ tail
 obtain ⟨reply,_,tail⟩:=FIv_Map.bind_success _ _ _ tail
 cases reply with
 | Err e=>
  simp [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame] at tail
 | Ok viewed=>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail
  obtain ⟨payload,parsed,tail⟩:=FIv_Map.bind_success _ _ _ tail
  cases payload with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame] at tail
  | Ok data =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail
    have framed : viewed=frame := tail.1
    subst frame
    exact ⟨data,parsed⟩
#print axioms result
end AspisR1.NIX_RecordAtOrigin
