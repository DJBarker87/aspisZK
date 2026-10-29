import R1Z.PV_RunJoin_PrepareTail48
import R1Z.PV_RunJoin_PreparedFields48
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareTailSuccess48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_PreparedDomain48 (W)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (q w : Slice W) (out : prover.PreparedOpening)
    (h : @PV_RunJoin_PrepareTail48.run (types base) (selected base heap box ops)
      variant hash backend sem transcript2 y1 gamma inactive kappa q w=ok (.Ok out)) :
    ∃ (c0 : Array W 7#usize) (bytes : alloc.vec.Vec U8) (a : W)
      (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (q1 w1 folded : alloc.vec.Vec W),
      @prover.round (types base) (selected base heap box ops) q w=ok c0 ∧
      @prover.encoded_slice (types base) (selected base heap box ops) (Array.to_slice c0)=ok bytes ∧
      @host_transcript.Transcript.scalar (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        transcript2 29#u8 (alloc.vec.Vec.deref bytes) false=ok (a,tr) ∧
      @prover.fold (types base) (selected base heap box ops) q a false=ok q1 ∧
      @prover.fold (types base) (selected base heap box ops) w a true=ok w1 ∧
      @host_commitment.EncodingDomain.evaluate (types base) (selected base heap box ops) _
        (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField (types base) (selected base heap box ops))
        backend.domain (alloc.vec.Vec.deref q1) 0#usize=ok (.Ok folded) ∧
      out.backend=backend ∧ out.sem=sem ∧ out.transcript=tr ∧ out.y1=y1 ∧
      out.gamma=gamma ∧ out.inactive=inactive ∧ out.kappa=kappa ∧ out.alpha0=a ∧
      out.c0bytes=bytes ∧ out.q1=q1 ∧ out.w1=w1 ∧ out.folded_word=folded := by
  unfold PV_RunJoin_PrepareTail48.run at h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨c0,hc,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  obtain ⟨bytes,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  obtain ⟨⟨a,tr⟩,ha,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  dsimp only [Aeneas.Std.uncurry] at h
  obtain ⟨q1,hq,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  obtain ⟨w1,hw,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  obtain ⟨folded,hd,hfields⟩ := PV_RunJoin_PreparedFields48.complete base heap box ops
    backend sem tr y1 gamma inactive kappa a bytes q1 w1 _ out h
  exact ⟨c0,bytes,a,tr,q1,w1,folded,hc,hb,ha,hq,hw,hd,hfields⟩
#print axioms complete
end R1Z.PV_RunJoin_PrepareTailSuccess48
