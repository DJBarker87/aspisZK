import R1Z.PV_RunJoin_CanonicalRecord43
import R1Z.PV_RunJoin_PostMap43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalAppend43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41 PV_RunJoin_CanonicalRecord43
variable [ExternalTypes]

theorem post (ops : ExternalFuns) {H : Type} (hash : aspis_core.digest.Digest32 H)
    (row tag : U8) (size : Usize) (payload : Slice U8)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=
      .ok (some (tag,size))) (length : payload.length=size.val)
    (room : out.length+5+size.val≤Usize.max)
    (high : PV_RunJoin_HighDomain40.HighZero payload.val) :
    Post (fun next : (core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
          host_wire.SemanticTranscript H × alloc.vec.Vec U8 =>
        match next.1 with
        | .Ok _ => Piece size.val out.val next.2.2.val
        | .Err _ => True)
      (@host_semantic.semantic_row _ (ProverRwP6BodyCandidate.selected ops)
        H hash row payload transcript out) := by
  have h := PV_RunJoin_RecordPost43.append ops hash row tag size payload transcript out shape length room
  apply PV_RunJoin_PostMap43.mono h
  intro next hn
  rcases next with ⟨status,t,o⟩
  cases status with
  | Err e => trivial
  | Ok q =>
    obtain ⟨header,hlen,hbytes,olen⟩ := hn
    exact ⟨header,payload.val,hlen,length,high,hbytes⟩
#print axioms post
end R1Z.PV_RunJoin_CanonicalAppend43
