import R1Z.PV_RunJoin_NativeArithmeticTrace69
import R1Z.PV_RunJoin_OpeningStreamUnique69
import R1Z.PV_RunJoin_OpeningEncoded44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeArithmeticImages69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open ProverCommitWideOps48 ProverCommitMix48
attribute [local irreducible] source sourceArray PV_RunJoin_FoldCell44.array
theorem complete {State Fail : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) State Fail)
    (world : PV_FXM_ReserveWorld.World State Fail)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts) (p : prover.Publication)
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared))
    (hs : letI : ExternalTypes := types base
      @prover.derive_private_salts (types base) (opsNative base heap box ops runtime world)
        phase.val.salts.1 phase.val.salts.2 phase.val.hash 114#u8=ok (.Ok salts))
    (hf : letI : ExternalTypes := types base
      @prover.finish_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash prepared salts=ok (.Ok p))
    (hc : letI : ExternalTypes := types base
      @PV_RunJoin_OpeningImages54.Coefficients
        (@PV_RunJoin_ActualRun.data (types base) (opsNative base heap box ops runtime world) phase.val))
    (images : @PV_RunJoin_OpeningImages54.Images
      (@PV_RunJoin_ActualRun.data (types base) (opsNative base heap box ops runtime world) phase.val) hc) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    PV_RunJoin_PublishSkeleton54.bytes p.c0bytes.val=PV_RunJoin_OpeningImages54.round0 (PV_RunJoin_ActualRun.data phase.val) ∧
    PV_RunJoin_PublishSkeleton54.bytes p.c1bytes.val=PV_RunJoin_OpeningImages54.round1 (PV_RunJoin_ActualRun.data phase.val) ∧
    PV_RunJoin_PublishSkeleton54.bytes p.fbytes.val=PV_RunJoin_OpeningImages54.finalBytes (PV_RunJoin_ActualRun.data phase.val) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  let d := PV_RunJoin_ActualRun.data phase.val
  obtain ⟨q,w,tr,claim,g,inactive,k,hq,hw,hqmodel,hwmodel,ht⟩ :=
    PV_RunJoin_NativeOpeningArrays69.complete base heap box ops runtime world phase prepared hp
  obtain ⟨first,second,fin,hrun,hb0,hb1,hbf⟩ :=
    PV_RunJoin_NativeArithmeticTrace69.complete base heap box ops runtime world phase prepared salts p
      hp hs hf q w hq tr claim g inactive k ht
  obtain ⟨hg,hk,ha,hb⟩ := PV_RunJoin_NativeFinishCanonical63.complete base heap box ops runtime world phase.val prepared hp
  obtain ⟨c0,q1,c1,finRaw,vq,vf,bc0,bc1,bfin,hcc0,hcc1,hcfin,
    hnative,hmodel,hbc0,hbc1,hbfin,hi0,hi1,hif⟩ :=
    @PV_RunJoin_OpeningEncoded44.complete (types base) (residual base ops runtime world)
      q w hq hw d.a d.b ha hb
  have eqNative := Result.ok.inj (hnative.symm.trans hrun)
  have efirst := congrArg (fun t => t.1) eqNative
  have esecond := congrArg (fun t => t.2.2.1) eqNative
  have efinal := congrArg (fun t => t.2.2.2) eqNative
  rw [←efirst] at hb0
  rw [←esecond] at hb1
  rw [←efinal] at hbf
  have bytes0 : bc0=p.c0bytes := Result.ok.inj (hbc0.symm.trans hb0)
  have bytes1 : bc1=p.c1bytes := Result.ok.inj (hbc1.symm.trans hb1)
  have bytesf : bfin=p.fbytes := Result.ok.inj (hbfin.symm.trans hbf)
  obtain ⟨m0,mq1,m1,mfin,hcm0,hcm1,hcmfin,hm,hm0,hm1,hmfin⟩ := images
  change ProverCommitOpeningModel53.run d.c hc
    (ProverCommitQArray48.array 10#usize d.p) (ProverCommitNativeQ48.source d.x0)
    (ProverCommitNativeQ48.source d.y0) (ProverCommitNativeQ48.source d.x1)
    (ProverCommitNativeQ48.source d.y1) (source d.g) (source d.k) (source d.a) (source d.b)=_ at hm
  simp only [ProverCommitOpeningModel53.run,hqmodel,hwmodel,bind_tc_ok] at hm
  have eqModel := Result.ok.inj (hmodel.symm.trans hm)
  have em0 := congrArg (fun t => t.1) eqModel
  have em1 := congrArg (fun t => t.2.2.1) eqModel
  have emfin := congrArg (fun t => t.2.2.2) eqModel
  have stream0 := PV_RunJoin_OpeningStreamUnique69.stream 7 c0 m0 hcc0 hcm0 em0
  have stream1 := PV_RunJoin_OpeningStreamUnique69.stream 7 c1 m1 hcc1 hcm1 em1
  have streamf := PV_RunJoin_OpeningStreamUnique69.stream 64 finRaw mfin hcfin hcmfin
    (congrArg Subtype.val emfin)
  rw [bytes0] at hi0
  rw [bytes1] at hi1
  rw [bytesf] at hif
  exact ⟨hi0.trans (stream0.trans hm0),hi1.trans (stream1.trans hm1),hif.trans (streamf.trans hmfin)⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeArithmeticImages69
