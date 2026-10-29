import R1Z.PV_RunJoin_PrepareTail48
import R1Z.PV_RunJoin_FirstArithmetic48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareTailAssociation48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)

 def retained [ExternalTypes] [ExternalFuns] (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (bytes : alloc.vec.Vec U8)
    (q w : Slice W) (fold : Slice W → W → Bool → Result (alloc.vec.Vec W)) := do
  let (alpha0,transcript3) ← host_transcript.Transcript.scalar
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 transcript2 29#u8 (alloc.vec.Vec.deref bytes) false
  let q1 ← fold q alpha0 false
  let w1 ← fold w alpha0 true
  PV_RunJoin_PreparedDomain48.run backend sem transcript3 y1 gamma inactive kappa alpha0 bytes q1 w1
    (host_commitment.EncodingDomain.evaluate
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField backend.domain (alloc.vec.Vec.deref q1) 0#usize)

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (q w : Nat → Raw)
    (hq : ∀ j,j<1024 → canonical (q j)) (hw : ∀ j,j<1024 → canonical (w j)) :
    ∃ (c0 : Nat → Raw) (bytes : alloc.vec.Vec U8) (hcc : ∀ j,j<7 → canonical (c0 j)),
      @PV_RunJoin_PrepareTail48.run (types base) (selected base heap box ops)
        variant hash backend sem transcript2 y1 gamma inactive kappa
        (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=
        @retained (types base) (selected base heap box ops) variant hash backend sem transcript2 y1 gamma inactive kappa bytes
          (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
          (@prover.fold (types base) (@ProverRwP6BodyCandidate.selected (types base) ops)) ∧
      ProverCommitRoundScaled48.run 256 (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
        ok (List.ofFn (fun i : Fin 7 => source (c0 i.val))) ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hcc := by
  obtain ⟨c0,hc0,hmodel,hcc⟩ := @PV_RunJoin_RoundAssociation44.complete (types base) ops 1024#usize (by decide) q w hq hw
  obtain ⟨bytes,hbytes,himage⟩ := @PV_RunJoin_EncodedImage43.encode (types base) ops 7#usize c0 hcc (by scalar_tac)
  have hc : @prover.round (types base) (selected base heap box ops)
      (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=ok (array 7#usize c0) := by
    rw [PV_RunJoin_RoundInstalled48.complete base heap box ops _ _ (@PV_RunJoin_SourceLength48.first (types base) q)]
    exact hc0
  have hb : @prover.encoded_slice (types base) (selected base heap box ops)
      (Array.to_slice (array 7#usize c0))=ok bytes := by
    rw [PV_RunJoin_EncodedInstalled48.complete base heap box ops]
    exact hbytes
  refine ⟨c0,bytes,hcc,?_,hmodel,himage⟩
  simp only [PV_RunJoin_PrepareTail48.run,hc,bind_tc_ok,lift,hb,retained,
    PV_RunJoin_FoldInstalled48.complete base heap box ops _ _ false (@PV_RunJoin_SourceLength48.first (types base) q),
    PV_RunJoin_FoldInstalled48.complete base heap box ops _ _ true (@PV_RunJoin_SourceLength48.first (types base) w)]
#print axioms retained
#print axioms complete
end R1Z.PV_RunJoin_PrepareTailAssociation48
