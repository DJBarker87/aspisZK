import R1Z.PV_RunJoin_RecordFrame41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecordAppend41
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]

theorem bind_post {A B : Type} {p : A → Prop} {q : B → Prop}
    {r : Result A} {f : A → Result B} (post : Post p r)
    (preserve : ∀ a, p a → Post q (f a)) : Post q (r >>= f) := by
  cases r with
  | ok a => exact preserve a post
  | fail e => trivial
  | div => trivial

/-- The actual caller semantic_row appends the original framed payload on
success. No transcript-hash, parser or semantic_row success is a premise. -/
theorem append (ops : ExternalFuns) {H : Type} (hash : aspis_core.digest.Digest32 H)
    (row tag : U8) (size : Usize) (payload : Slice U8)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=
      .ok (some (tag,size))) (length : payload.length=size.val)
    (room : out.length+5+size.val≤Usize.max) :
    ∃ header : List U8, header.length=5 ∧
      Post (fun next : (core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
          (host_wire.SemanticTranscript H) × (alloc.vec.Vec U8) =>
        match next.1 with
        | .Ok _ => next.2.2.val=out.val ++ header ++ payload.val
        | .Err _ => True)
      (@host_semantic.semantic_row _ (ProverRwP6BodyCandidate.selected ops)
        H hash row payload transcript out) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  obtain ⟨header,framed,hlen,hbytes,hpost⟩ := PV_RunJoin_RecordFrame41.frame ops row tag size
    payload shape length (by omega)
  have flen : framed.length=5+size.val := by
    change framed.val.length=5+size.val
    rw [hbytes,List.length_append,hlen]
    exact congrArg (fun n => 5+n) length
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_ByteAppend38.append out (alloc.vec.Vec.deref framed)
    (by change out.length+framed.length≤Usize.max;rw [flen];omega)
  refine ⟨header,hlen,?_⟩
  unfold host_semantic.semantic_row
  apply bind_post hpost
  intro status hs
  cases status with
  | Err e => trivial
  | Ok value =>
    change value=framed at hs
    subst value
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro pair
    rcases pair with ⟨result,state⟩
    cases result with
    | Err e => trivial
    | Ok q =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,hn,Post]
      rw [hv]
      change out.val ++ framed.val=out.val ++ header ++ payload.val
      rw [hbytes,List.append_assoc]
#print axioms bind_post
#print axioms append
end R1Z.PV_RunJoin_RecordAppend41
