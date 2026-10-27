import XRu_ParserShapes
import XRk_ResultTools
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRu_RecordCuts
/-- Small frame prefix isolated after the broad transport hit heartbeats.
Every witness is obtained from the SAME actual record computation. -/
theorem source (row : U8) (bytes payload : Slice U8)
 (run : r1_wire.parse_record row bytes=ok (.Ok payload)) :
 ∃ (tag : U8) (size full : Usize),
 r1_wire.row_shape row=ok (some (tag,size)) ∧
 (5#usize+size : Result Usize)=ok full ∧
 Slice.len bytes=full ∧ Slice.index_usize bytes 0#usize=ok tag := by
 unfold r1_wire.parse_record at run
 obtain ⟨o,ho,run⟩ := bind_success _ _ _ run
 cases o with
 | none =>
  simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from] at run
 | some pair =>
  rcases pair with ⟨tag,size⟩
  simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
  obtain ⟨full,hfull,run⟩ := bind_success _ _ _ run
  dsimp only at run
  split at run
  · cases run
  · rename_i hframe
    have frame : Slice.len bytes=full := by simpa only [bne_iff_ne,not_not] using hframe
    obtain ⟨actual,htag,run⟩ := bind_success _ _ _ run
    split at run
    · cases run
    · rename_i heq
      have same : actual=tag := by simpa only [bne_iff_ne,not_not] using heq
      exact ⟨tag,size,full,ho,hfull,frame,by simpa only [same] using htag⟩
#print axioms source
end XRu_RecordCuts
