import NGX_RunBind
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NGX_Validated
abbrev T (H : Type) := r1_wire.SemanticTranscript H
abbrev Q := aspis_core.field.QM31

def computation {H : Type}
 (sample : T H→U8→Slice U8→Result (core.result.Result (Array U8 32#usize) r1_wire.Error×T H))
 (self : T H) (record1 : r1_wire.ValidatedRecord) :
 Result (core.result.Result Q r1_wire.Error×T H) := do
 let row←r1_wire.ValidatedRecord.impl.row record1
 if row>24#u8 then ok (.Err .InvalidRow,self) else do
 let frame←r1_wire.ValidatedRecord.impl.framed record1
 let (reply,after)←sample self row frame
 match reply with
 | .Err error=>ok (.Err error,after)
 | .Ok block=>do
   let q←AspisR1PublicPreparation.sampler.qm31_sample block
   ok (.Ok q,after)

theorem source {H : Type} (D : aspis_core.Digest32 H) (self : T H) (record1 : r1_wire.ValidatedRecord) :
 r1_wire.SemanticTranscript.semantic_validated D self record1=
 computation (r1_wire.SemanticTranscript.sample_block_validated D) self record1 := by
 unfold r1_wire.SemanticTranscript.semantic_validated computation
 cases h : r1_wire.ValidatedRecord.impl.row record1 <;> simp only [h,bind_tc_fail,bind_tc_div,bind_tc_ok]
 rename_i row
 split <;> (try rfl)
 cases f : r1_wire.ValidatedRecord.impl.framed record1 <;> simp only [f,bind_tc_fail,bind_tc_div,bind_tc_ok]
 rename_i frame
 cases s : r1_wire.SemanticTranscript.sample_block_validated D self row frame <;> simp only [s,bind_tc_fail,bind_tc_div,bind_tc_ok]
 rename_i pair
 rcases pair with ⟨reply,after⟩
 cases reply <;> rfl

theorem sample_domain (record1 : r1_wire.ValidatedRecord) (row : U8)
 (same : r1_wire.ValidatedRecord.impl.row record1=ok row)
 (allowed : row.val≤24) (frame_bound : record1.framed.val.length≤3717) :
 row.val≤26 ∧ record1.framed.val.length≤3717 := by omega

/-- Child failures preserve the exact source error and child-produced state. -/
theorem error_continuation {H : Type} (error : r1_wire.Error) (after : T H) :
 (do
  let cf←core.result.Result.Insts.CoreOpsTry.branch (.Err error : core.result.Result (Array U8 32#usize) r1_wire.Error)
  match cf with
  | .Continue block=>do
    let q←AspisR1PublicPreparation.sampler.qm31_sample block
    ok (.Ok q,after)
  | .Break residual=>do
    let r←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Q (core.convert.FromSame r1_wire.Error) residual
    ok (r,after))=ok (.Err error,after) := by rfl

#print axioms source
#print axioms sample_domain
#print axioms error_continuation
end AspisR1.NGX_Validated
