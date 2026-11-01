import R1Z.PV_RunJoin_CoefficientTable69
import R1Z.PV_RunJoin_CircleCanonical69
import R1Z.PV_RunJoin_NativeBinding63
import R1Z.PV_RunJoin_NativeFinishCanonical63
import R1Z.PV_RunJoin_PrepareTailSuccess48
import R1Z.PV_RunJoin_FoldCell44
import R1Z.PV_RunJoin_ActualScalar60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeOpeningArrays69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (fromW toW)
open ProverCommitWideOps48 ProverCommitMix48
attribute [local irreducible] source sourceArray PV_RunJoin_FoldCell44.array
  ProverCommitArray49.array ProverCommitGammaCell53.table

theorem image (n : Usize) (q : Nat → Raw) :
    amap fromW (sourceArray n q)=PV_RunJoin_FoldCell44.array n q := by
  apply Subtype.ext
  simp only [amap,sourceArray,PV_RunJoin_FoldCell44.array,ProverCommitArray49.array,List.map_ofFn]
  rfl

theorem complete {State Fail : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) State Fail)
    (world : PV_FXM_ReserveWorld.World State Fail)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (prepared : prover.PreparedOpening)
    (hp : letI : ExternalTypes := types base
      @prover.prepare_opening (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem=ok (.Ok prepared)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ (q w : Nat → Raw) (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (claim : alloc.vec.Vec U8) (g inactive k : aspis_core.field.wide_exact.WideExact),
      (∀ j,j<1024 → canonical (q j)) ∧ (∀ j,j<1024 → canonical (w j)) ∧
      ProverCommitGammaOutput53.run
        (ProverCommitGammaCell53.table (ProverCommitGammaCoefficients53.wide
          (PV_RunJoin_ActualRun.data phase.val).c (PV_RunJoin_ActualData59.canonical_coefficients phase.val)))
        (source (PV_RunJoin_ActualRun.data phase.val).g)=ok (sourceArray 1024#usize q) ∧
      ProverCommitWeightsMaterial53.run
        (ProverCommitQArray48.array 10#usize (PV_RunJoin_ActualRun.data phase.val).p)
        (ProverCommitNativeQ48.source (PV_RunJoin_ActualRun.data phase.val).x0)
        (ProverCommitNativeQ48.source (PV_RunJoin_ActualRun.data phase.val).y0)
        (ProverCommitNativeQ48.source (PV_RunJoin_ActualRun.data phase.val).x1)
        (ProverCommitNativeQ48.source (PV_RunJoin_ActualRun.data phase.val).y1)
        (source (PV_RunJoin_ActualRun.data phase.val).k)=ok (sourceArray 1024#usize w) ∧
      PV_RunJoin_PrepareTail48.run .S2 phase.val.hash phase.val.backend phase.val.sem
        tr claim g inactive k (Array.to_slice (PV_RunJoin_FoldCell44.array 1024#usize q))
          (Array.to_slice (PV_RunJoin_FoldCell44.array 1024#usize w))=ok (.Ok prepared) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  let d := PV_RunJoin_ActualRun.data phase.val
  let hc := PV_RunJoin_ActualData59.canonical_coefficients phase.val
  obtain ⟨coeff,kw,qs,ws,tr,claim,g,inactive,k,hlen,hcoeff,hq,hw,hbox,hheap,ht⟩ :=
    PV_RunJoin_NativePreparedArrays66.complete base heap box ops runtime world phase prepared hp
  have matrix := PV_RunJoin_NativeBackendMatrix66.complete base heap box ops runtime world phase
  rw [matrix] at hcoeff
  have htable := PV_RunJoin_CoefficientTable69.table d.c hc coeff hlen hcoeff
  obtain ⟨c0,bc0,a,tr3,q1,w1,folded,hr0,hbc0,ha,hq1,hw1,hfolded,
    hb,hs,ht3,hclaim,hg,hi,hk,haa,hbytes,hqq,hww,hff⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world) .S2 phase.val.hash phase.val.backend phase.val.sem
      tr claim g inactive k _ _ prepared ht
  obtain ⟨hg',hk',ha'⟩ := PV_RunJoin_ActualScalar60.prepared phase.val prepared hp
  change fromW (source d.g)=prepared.gamma at hg'
  change fromW (source d.k)=prepared.kappa at hk'
  have gs : source d.g=toW g := by
    simpa only [ProverRwDictionaryTower.native_w_roundtrip] using congrArg toW (hg'.trans hg)
  have ks : source d.k=toW k := by
    simpa only [ProverRwDictionaryTower.native_w_roundtrip] using congrArg toW (hk'.trans hk)
  have native := PV_RunJoin_NativeBinding63.native base heap box ops runtime world
  let value : @PV_RunJoin_NativeControl55.Phase (types base) := phase.val
  let p : PV_RunJoin_NativeActual62.P base heap box (PV_RunJoin_NativeBinding63.remaining base ops runtime world) :=
    ⟨phase.val,by
      change @PV_RunJoin_ActualProvenance60.Produced (types base)
        (PV_RunJoin_NativeResidual62.opsNative base heap box
          (PV_RunJoin_NativeBinding63.remaining base ops runtime world)) value
      rw [←native]
      exact phase.property⟩
  have domain := PV_RunJoin_CircleCanonical69.data base heap box
    (PV_RunJoin_NativeBinding63.remaining base ops runtime world) p
  change (∀ i,i<10 → ProverCommitSubfieldOps47.Canonical (d.p i)) ∧
    ProverCommitSubfieldOps47.Canonical d.x0 ∧ ProverCommitSubfieldOps47.Canonical d.y0 ∧
    ProverCommitSubfieldOps47.Canonical d.x1 ∧ ProverCommitSubfieldOps47.Canonical d.y1 at domain
  obtain ⟨hpoint,hx0,hy0,hx1,hy1⟩ := domain
  obtain ⟨hgcan,hkcan,hacan,hbcan⟩ :=
    PV_RunJoin_NativeFinishCanonical63.complete base heap box ops runtime world phase.val prepared hp
  obtain ⟨q,hqmodel,hcq,hdq⟩ := ProverCommitGammaOutput53.exact_result
    (ProverCommitGammaCoefficients53.wide d.c hc)
    (ProverCommitGammaCoefficients53.wide_canonical d.c hc) d.g hgcan
  obtain ⟨w,hwmodel,hcw,hdw⟩ := ProverCommitWeightsMaterial53.exact_result d.p hpoint
    d.x0 d.y0 d.x1 d.y1 hx0 hy0 hx1 hy1 d.k hkcan
  rw [htable,← gs,hqmodel] at hq
  have eqQ : qs=sourceArray 1024#usize q := (Result.ok.inj hq).symm
  change ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize d.p)
    (ProverCommitNativeQ48.source d.x0) (ProverCommitNativeQ48.source d.y0)
    (ProverCommitNativeQ48.source d.x1) (ProverCommitNativeQ48.source d.y1) (toW k)=ok ws at hw
  rw [←ks,hwmodel] at hw
  have eqW : ws=sourceArray 1024#usize w := (Result.ok.inj hw).symm
  rw [eqQ,eqW,image,image] at ht
  exact ⟨q,w,tr,claim,g,inactive,k,hcq,hcw,hqmodel,hwmodel,ht⟩

#print axioms image
#print axioms complete
end R1Z.PV_RunJoin_NativeOpeningArrays69
