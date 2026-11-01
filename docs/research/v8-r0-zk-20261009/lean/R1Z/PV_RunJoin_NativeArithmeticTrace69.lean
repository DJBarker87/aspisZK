import R1Z.PV_RunJoin_NativeOpeningArrays69
import R1Z.PV_RunJoin_NativeFinalFold63
import R1Z.PV_RunJoin_FinishFrame63
import R1Z.PV_RunJoin_FirstArithmetic48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeArithmeticTrace69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open ProverCommitWideOps48 ProverCommitMix48
open PV_RunJoin_FoldCell44 (array)
attribute [local irreducible] source sourceArray array

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
    (q w : Nat → Raw) (hq : ∀ j,j<1024 → canonical (q j))
    (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (claim : alloc.vec.Vec U8) (g inactive k : aspis_core.field.wide_exact.WideExact)
    (ht : letI : ExternalTypes := types base
      @PV_RunJoin_PrepareTail48.run (types base) (opsNative base heap box ops runtime world)
        .S2 phase.val.hash phase.val.backend phase.val.sem tr claim g inactive k
        (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=ok (.Ok prepared)) :
    letI : ExternalTypes := types base
    ∃ (first second : Array aspis_core.field.wide_exact.WideExact 7#usize)
      (fin : alloc.vec.Vec aspis_core.field.wide_exact.WideExact),
      PV_RunJoin_OpeningKernel44.run (residual base ops runtime world)
        (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
        (ProverRwDictionaryTower.fromW (source (@PV_RunJoin_ActualRun.data (types base)
          (opsNative base heap box ops runtime world) phase.val).a))
        (ProverRwDictionaryTower.fromW (source (@PV_RunJoin_ActualRun.data (types base)
          (opsNative base heap box ops runtime world) phase.val).b))=ok (first,prepared.q1,second,fin) ∧
      @prover.encoded_slice (types base) (ProverRwP6BodyCandidate.selected (residual base ops runtime world))
        (Array.to_slice first)=ok p.c0bytes ∧
      @prover.encoded_slice (types base) (ProverRwP6BodyCandidate.selected (residual base ops runtime world))
        (Array.to_slice second)=ok p.c1bytes ∧
      @prover.encoded_slice (types base) (ProverRwP6BodyCandidate.selected (residual base ops runtime world))
        (alloc.vec.Vec.deref fin)=ok p.fbytes := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨first,bc0,a,tr3,q1,w1,folded,hr0,hbc0,hat,hq1,hw1,hfolded,
    hb,hsem,ht3,hclaim,hg,hi,hk,haa,hbytes,hqq,hww,hff⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world) .S2 phase.val.hash phase.val.backend phase.val.sem
      tr claim g inactive k _ _ prepared ht
  obtain ⟨hg',hk',ha⟩ := PV_RunJoin_ActualScalar60.prepared phase.val prepared hp
  rw [←hqq,←haa,←ha] at hq1
  rw [←hww,←haa,←ha] at hw1
  rw [PV_RunJoin_RoundInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _ _ (PV_RunJoin_SourceLength48.first q)] at hr0
  rw [PV_RunJoin_FoldInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _ _ false (PV_RunJoin_SourceLength48.first q)] at hq1
  rw [PV_RunJoin_FoldInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _ _ true (PV_RunJoin_SourceLength48.first w)] at hw1
  have hca := (PV_RunJoin_NativeFinishCanonical63.complete base heap box ops runtime world phase.val prepared hp).2.2.1
  obtain ⟨r,v,hfold,hmodel,himage,hcr,hdr⟩ := @PV_RunJoin_PrimalFirst44.complete
    (types base) (residual base ops runtime world) q hq (PV_RunJoin_ActualRun.data phase.val).a hca
  have veq : v=prepared.q1 := Result.ok.inj (hfold.symm.trans hq1)
  have small : (alloc.vec.Vec.deref prepared.q1).length/4≤256 := by
    rw [←veq,←himage]
    exact PV_RunJoin_SourceLength48.second r
  obtain ⟨second,fin,hr1,hbc1,hfin,hbf,hcb⟩ :=
    PV_RunJoin_NativeFinalFold63.complete base heap box ops runtime world phase prepared salts p hp hs hf
  have hr1' := (PV_RunJoin_RoundInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _ _ small).symm.trans hr1
  have hfin' := (PV_RunJoin_FoldInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _ _ false small).symm.trans hfin
  have hbc0' := (PV_RunJoin_EncodedInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _).symm.trans hbc0
  have hbc1' := (PV_RunJoin_EncodedInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _).symm.trans hbc1
  have hbf' := (PV_RunJoin_EncodedInstalled48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world) _).symm.trans hbf
  have frame := (PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prepared salts p hf).2.2.2.2.1
  refine ⟨first,second,fin,?_,?_,hbc1',hbf'⟩
  · simp only [PV_RunJoin_OpeningKernel44.run,hr0,hq1,hw1,hr1',hfin',bind_tc_ok]
  · rw [frame,hbytes]
    exact hbc0'

#print axioms complete
end R1Z.PV_RunJoin_NativeArithmeticTrace69
