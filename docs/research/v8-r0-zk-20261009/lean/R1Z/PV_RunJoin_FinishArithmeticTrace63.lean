import R1Z.PV_RJQ_FinishTrace
import R1Z.PV_RunJoin_ActualScalar60
import R1Z.PV_RunJoin_ActualPublication60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FinishArithmeticTrace63
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
variable [ExternalTypes] [ExternalFuns]

theorem complete (phase : PV_RunJoin_NativeControl55.Phase) (prepared : prover.PreparedOpening)
    (salts : host_commitment.PrivateSalts) (p : prover.Publication)
    (hp : prover.prepare_opening .S2 phase.hash phase.backend phase.sem=ok (.Ok prepared))
    (hs : prover.derive_private_salts phase.salts.1 phase.salts.2 phase.hash 114#u8=ok (.Ok salts))
    (hf : prover.finish_opening .S2 phase.hash prepared salts=ok (.Ok p)) :
    ∃ (second : Array W 7#usize) (alpha : W) (next : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (payload0 payload : alloc.vec.Vec U8) (final : alloc.vec.Vec W),
      prover.round (alloc.vec.Vec.deref prepared.q1) (alloc.vec.Vec.deref prepared.w1)=ok second ∧
      prover.encoded_slice (Array.to_slice second)=ok p.c1bytes ∧
      alloc.slice.Slice.to_vec core.clone.CloneU8 (Array.to_slice p.root)=ok payload0 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload0 (alloc.vec.Vec.deref p.c1bytes)=ok payload ∧
      host_transcript.Transcript.scalar aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prepared.transcript 30#u8 (alloc.vec.Vec.deref payload) false=ok (alpha,next) ∧
      PV_RunJoin_ActualRunSources59.alpha1 phase=ok (some alpha) ∧
      ProverRwDictionaryTower.fromW (ProverCommitWideOps48.source (PV_RunJoin_ActualRun.data phase).b)=alpha ∧
      prover.fold (alloc.vec.Vec.deref prepared.q1) alpha false=ok final ∧
      prover.encoded_slice (alloc.vec.Vec.deref final)=ok p.fbytes := by
  obtain ⟨leaves,o,tree,root,second,cbytes,payload0,payload,alpha,next,final,fbytes,queries,tr,
    hleaves,htree,ho,hroot,hsecond,hcbytes,hpayload0,hpayload,hscalar,hfinal,hfbytes,hqueries,hpublication⟩ :=
      PV_RJQ_FinishTrace.source .S2 phase.hash prepared salts p hf
  have hprepare : PV_RunJoin_ActualRunSources59.prepare phase=ok (.Ok prepared) := hp
  have hsalts : PV_RunJoin_ActualRunSources59.salts phase=ok (.Ok salts) := hs
  have hfinish := PV_RunJoin_ActualRunSources59.finish_return phase prepared salts p hprepare hsalts hf
  have halpha : PV_RunJoin_ActualRunSources59.alpha1 phase=ok (some alpha) := by
    simp only [PV_RunJoin_ActualRunSources59.alpha1,hprepare,hfinish,bind_tc_ok,
      hpublication,lift,hpayload0,hpayload,hscalar]
    rfl
  have hb : ProverRwDictionaryTower.fromW
      (ProverCommitWideOps48.source (PV_RunJoin_ActualRun.data phase).b)=alpha := by
    simp only [PV_RunJoin_ActualRun.data,PV_RunJoin_ActualData59.data,
      PV_RunJoin_ActualData59.finalScalar,halpha,PV_RunJoin_ActualScalar60.raw_roundtrip]
  refine ⟨second,alpha,next,payload0,payload,final,hsecond,?_,?_,?_,hscalar,halpha,hb,hfinal,?_⟩
  · simpa only [hpublication] using hcbytes
  · simpa only [hpublication] using hpayload0
  · simpa only [hpublication] using hpayload
  · simpa only [hpublication] using hfbytes

#print axioms complete
end R1Z.PV_RunJoin_FinishArithmeticTrace63
