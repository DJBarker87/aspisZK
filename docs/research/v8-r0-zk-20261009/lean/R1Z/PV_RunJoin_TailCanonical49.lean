import R1Z.PV_RunJoin_TailScalar49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TailCanonical49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)

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
        @PV_RunJoin_TailScalar49.after (types base) (selected base heap box ops) backend sem y1 gamma inactive kappa bytes
          (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
          (@prover.fold (types base) (@ProverRwP6BodyCandidate.selected (types base) ops))
          (PV_RunJoin_ScalarSource49.retained base heap box ops
            (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
            transcript2 29#u8 (alloc.vec.Vec.deref bytes) false) ∧
      ProverCommitRoundScaled48.run 256 (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
        ok (List.ofFn (fun i : Fin 7 => source (c0 i.val))) ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hcc := by
  obtain ⟨c0,bytes,hc0,heq,hround,hbytes⟩ := PV_RunJoin_PrepareTailAssociation48.complete
    base heap box ops variant hash backend sem transcript2 y1 gamma inactive kappa q w hq hw
  refine ⟨c0,bytes,hc0,?_,hround,hbytes⟩
  rw [heq,PV_RunJoin_TailScalar49.complete]
#print axioms complete
end R1Z.PV_RunJoin_TailCanonical49
