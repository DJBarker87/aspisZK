import R1Z.PV_RunJoin_ZeroRows43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroComplete43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41 PV_RunJoin_ByteExtension43
variable [ExternalTypes]

theorem post (ops : ExternalFuns) {H : Type} (hash : aspis_core.digest.Digest32 H)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (room : out.length+50≤Usize.max) :
    Post (fun next : (core.result.Result (Array aspis_core.field.QM31 10#usize) r1_wire.Error) ×
      host_wire.SemanticTranscript H × alloc.vec.Vec U8 =>
      match next.1 with | .Ok _ => Ext out.val next.2.2.val 50 | .Err _ => True)
      (@host_semantic.zc_rows _ (ProverRwP6BodyCandidate.selected ops) H hash transcript out) := by
  unfold host_semantic.zc_rows
  apply PV_RunJoin_ResultPost41.bind
  intro zero
  have post := PV_RunJoin_ZeroRows43.loop ops hash 10 0#usize transcript out
    (Array.repeat 10#usize zero) rfl (by simpa using room)
  apply PV_RunJoin_RecordAppend41.bind_post post
  intro result hr
  rcases result with ⟨t,o,z,pending⟩
  cases pending with
  | none => exact hr
  | some status =>
    cases status with
    | Err e => trivial
    | Ok value => exact hr
#print axioms post
end R1Z.PV_RunJoin_ZeroComplete43
