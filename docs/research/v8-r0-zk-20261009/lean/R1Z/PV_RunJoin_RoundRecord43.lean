import R1Z.PV_RunJoin_RoundShapes43
import R1Z.PV_RunJoin_PolyArrayCanonical41
import R1Z.PV_RunJoin_PostMap43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundRecord43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

def Added (before after : List U8) : Prop :=
  ∃ header payload : List U8, header.length=5 ∧ payload.length=896 ∧
    PV_RunJoin_HighDomain40.HighZero payload ∧ after=before++header++payload

theorem post (ops : ExternalFuns) {H F : Type} (hash : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle F) (oracle : F) (round : Usize) (small : round.val<10)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (room : out.length+901≤Usize.max) :
    Post (fun next : (core.result.Result (Array Q 10#usize × Q) r1_wire.Error) ×
          host_wire.SemanticTranscript H × alloc.vec.Vec U8 =>
      match next.1 with
      | .Ok _ => Added out.val next.2.2.val
      | .Err _ => True)
      (@host_sumcheck.prove_sumcheck_round _ (ProverRwP6BodyCandidate.selected ops)
        H F hash oi transcript out point running round oracle) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  unfold host_sumcheck.prove_sumcheck_round
  simp only [lift,bind_tc_ok]
  apply PV_RunJoin_ResultPost41.bind
  intro zero
  apply PV_RunJoin_ResultPost41.bind
  intro evaluations
  apply PV_RunJoin_ResultPost41.bind
  intro merged
  cases merged with
  | Err e => trivial
  | Ok values =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro polynomial
    apply PV_RunJoin_ResultPost41.bind
    intro boundary
    apply PV_RunJoin_ResultPost41.bind
    intro different
    cases different with
    | true => trivial
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      obtain ⟨payload,hp,plen,phigh⟩ := PV_RunJoin_PolyArrayCanonical41.encode ops polynomial
      rw [hp]
      simp only [bind_tc_ok,lift]
      obtain ⟨header,framed,hlen,fbytes,fpost⟩ := PV_RunJoin_RecordFrame41.frame ops
        (U8.wrapping_add 15#u8 (UScalar.cast .U8 round)) 2#u8 896#usize
        (alloc.vec.Vec.deref payload) (PV_RunJoin_RoundShapes43.shape ops round small)
        plen (by scalar_tac)
      apply PV_RunJoin_RecordAppend41.bind_post fpost
      intro recorded hr
      cases recorded with
      | Err e => trivial
      | Ok value =>
        change value=framed at hr
        subst value
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
        apply PV_RunJoin_ResultPost41.bind
        intro challenge
        rcases challenge with ⟨r,t⟩
        cases r with
        | Err e => trivial
        | Ok q =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply PV_RunJoin_ResultPost41.bind
          intro nextPoint
          have flen : framed.length=901 := by
            change framed.val.length=901
            rw [fbytes,List.length_append,hlen]
            change 5+payload.length=901
            omega
          obtain ⟨next,hn,hv⟩ := PV_RunJoin_ByteAppend38.append out
            (alloc.vec.Vec.deref framed) (by change out.length+framed.length≤Usize.max;rw [flen];exact room)
          rw [hn]
          simp only [bind_tc_ok]
          apply PV_RunJoin_ResultPost41.bind
          intro pointValue
          apply PV_RunJoin_ResultPost41.bind
          intro runningValue
          refine ⟨header,payload.val,hlen,plen,phigh,?_⟩
          rw [hv,fbytes,List.append_assoc]
#print axioms post
end R1Z.PV_RunJoin_RoundRecord43
