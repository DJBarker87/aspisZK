import R1Z.PV_RunJoin_RecordAppend41
import R1Z.PV_RunJoin_HighDomain40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecordPost43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]

theorem append (ops : ExternalFuns) {H : Type} (hash : aspis_core.digest.Digest32 H)
    (row tag : U8) (size : Usize) (payload : Slice U8)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=
      .ok (some (tag,size))) (length : payload.length=size.val)
    (room : out.length+5+size.val≤Usize.max) :
    Post (fun next : (core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
          (host_wire.SemanticTranscript H) × (alloc.vec.Vec U8) =>
        match next.1 with
        | .Ok _ => ∃ header : List U8, header.length=5 ∧
          next.2.2.val=out.val ++ header ++ payload.val ∧
          next.2.2.length=out.length+5+size.val
        | .Err _ => True)
      (@host_semantic.semantic_row _ (ProverRwP6BodyCandidate.selected ops)
        H hash row payload transcript out) := by
  obtain ⟨header,hlen,hpost⟩ := PV_RunJoin_RecordAppend41.append ops hash row tag size
    payload transcript out shape length room
  generalize he : @host_semantic.semantic_row _ (ProverRwP6BodyCandidate.selected ops)
    H hash row payload transcript out = result at *
  cases result with
  | fail e => trivial
  | div => trivial
  | ok next =>
    rcases next with ⟨status,t,o⟩
    cases status with
    | Err e => trivial
    | Ok q =>
      refine ⟨header,hlen,hpost,?_⟩
      change o.val.length=out.val.length+5+size.val
      rw [hpost,List.length_append,List.length_append,hlen]
      exact congrArg (fun n => out.val.length+5+n) length
#print axioms append
end R1Z.PV_RunJoin_RecordPost43
