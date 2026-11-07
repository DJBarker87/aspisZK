import NMO_PrefixBounds
import NGX_RecordAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_PrefixStep
open Aeneas Aeneas.Std Result AspisR1PrefixAggregateParser
/-- A successful original record step exposes the exact checked input window.
No payload decoder, field operation or chosen replacement record is unfolded. -/
theorem geometry (bytes framed : Slice U8) (row : U8) (offset finish : Usize)
 (run : r1_wire.parse_record_at bytes row offset=ok (.Ok (framed,finish))) :
 finish.val=offset.val+NGX_PrefixGeometry.width row.val ∧
 offset.val≤finish.val ∧ finish.val≤bytes.val.length ∧
 framed.val=List.slice offset.val finish.val bytes.val := by
 have framing := NIX_PredecessorFrames.record_at bytes framed row offset finish run
 rw [NGX_RecordAt.source] at run
 unfold NGX_RecordAt.computation at run
 obtain ⟨shape,_,tail⟩ := FIv_Map.bind_success _ _ _ run
 obtain ⟨pair,_,tail⟩ := FIv_Map.bind_success _ _ _ tail
 rcases pair with ⟨tag,size⟩
 change ((5#usize+size : Result Usize) >>= _) =
  (ok (.Ok (framed,finish)) : Result (core.result.Result (Slice U8×Usize) r1_wire.Error)) at tail
 obtain ⟨length,_,tail⟩ := FIv_Map.bind_success _ _ _ tail
 obtain ⟨next,_,tail⟩ := FIv_Map.bind_success _ _ _ tail
 obtain ⟨candidate,getCall,tail⟩ := FIv_Map.bind_success _ _ _ tail
 obtain ⟨reply,converted,tail⟩ := FIv_Map.bind_success _ _ _ tail
 cases reply with
 | Err e =>
  simp [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame] at tail
 | Ok viewed =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail
  obtain ⟨parsed,_,tail⟩ := FIv_Map.bind_success _ _ _ tail
  cases parsed with
  | Err e =>
   simp [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at tail
  | Ok payload =>
   simp [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at tail
   rcases tail with ⟨sameFrame,sameFinish⟩
   subst framed
   subst finish
   have actualGet : core.slice.Slice.get
    (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
    {start:=offset,«end»:=next}=ok (some viewed) := by
    cases candidate with
    | none => cases converted
    | some value =>
     have same : value=viewed := core.result.Result.Ok.inj (Result.ok.inj converted)
     cases same
     exact getCall
   simp only [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.get] at actualGet
   split at actualGet
   next valid =>
    have low : offset.val≤next.val := valid.1
    have high : next.val≤bytes.val.length := valid.2
    have same := Option.some.inj (Result.ok.inj actualGet)
    have data : viewed.val=List.slice offset.val next.val bytes.val :=
     (congrArg (fun s : Slice U8 => s.val) same).symm
    have extent : viewed.val.length=next.val-offset.val := by
     rw [data]
     simp only [List.slice,List.length_drop,List.length_take]
     omega
    exact ⟨by omega,low,high,data⟩
   next invalid => cases actualGet
#print axioms geometry
set_option pp.proofs false in #print geometry
end AspisR1.NMO_PrefixStep
end
