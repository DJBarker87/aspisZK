import R1Z.PV_RunJoin_TailModelSuccess49
import R1Z.PV_RunJoin_FirstRoundModel50
import R1Z.PV_RunJoin_ScalarSuccessModel50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TailDecoderModel50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (q w : Nat → Raw)
    (hq : ∀ j,j<1024 → canonical (q j)) (hw : ∀ j,j<1024 → canonical (w j))
    (out : prover.PreparedOpening)
    (h : @PV_RunJoin_PrepareTail48.run (types base) (selected base heap box ops) variant hash backend sem
      tr y1 gamma inactive kappa (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))=ok (.Ok out)) :
    ∃ (q1 w1 : Nat → Raw) (alpha : Raw) (block : Array U8 32#usize),
      canonical alpha ∧ out.alpha0=current (source alpha) ∧
      @host_transcript.Transcript.block _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        tr 29#u8 (alloc.vec.Vec.deref out.c0bytes)=ok (block,out.transcript) ∧
      value alpha=PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer block) ∧
      Array.to_slice (array 256#usize q1)=alloc.vec.Vec.deref out.q1 ∧
      Array.to_slice (array 256#usize w1)=alloc.vec.Vec.deref out.w1 ∧
      (∀ j,j<256 → canonical (q1 j) ∧ canonical (w1 j)) ∧
      (∀ i : Fin 256,value (q1 i.val)=AspisR1.RoundPairing.primalFold
        (PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer block))
        (fun j : Fin 1024 => value (q j.val)) i) ∧
      (∀ i : Fin 256,value (w1 i.val)=AspisR1.RoundPairing.dualFold
        (PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer block))
        (fun j : Fin 1024 => value (w j.val)) i) ∧
      out.c0bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.modelStream 7
        (fun i => (AspisR1.RoundPairing.roundPolynomial (n:=256)
          (fun j => value (q j.val)) (fun j => value (w j.val))).coeff i.val) := by
  obtain ⟨unused,q1,w1,c0,alpha,hc0,hca,halpha,hiq,hiw,hc,hqm,hwm,hbytes⟩ :=
    PV_RunJoin_TailModelSuccess49.complete base heap box ops variant hash backend sem tr y1 gamma inactive kappa q w hq hw out h
  obtain ⟨actualC0,bytes,actualAlpha,next,vq,vw,folded,hr,he,hs,hfq,hfw,hd,hfields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete base heap box ops variant hash backend sem tr y1 gamma inactive kappa
      (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w)) out h
  obtain ⟨block,a,hblock,hca',ha,hvalue⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr 2 29#u8 (alloc.vec.Vec.deref bytes) actualAlpha next hs
  rcases hfields with ⟨hb,hm,ht,hy,hg,hi,hk,haout,hbc,hqo,hwo,hfo⟩
  have same : alpha=a := PV_RunJoin_ScalarRaw50.injective (halpha.symm.trans (haout.trans ha))
  have meaning : value alpha=PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer block) := by
    rw [same];exact hvalue
  obtain ⟨c,modelBytes,hcc,hround,henc,hmodel,hcoeff,hmodelBytes⟩ :=
    PV_RunJoin_FirstRoundModel50.complete base heap box ops q w hq hw
  have ec : actualC0=array 7#usize c := Result.ok.inj (hr.symm.trans hround)
  rw [ec] at he
  have eb : bytes=modelBytes := Result.ok.inj (he.symm.trans henc)
  refine ⟨q1,w1,alpha,block,hca,halpha,?_,meaning,hiq,hiw,hc,?_,?_,?_⟩
  · rw [hbc,ht];exact hblock
  · simpa only [meaning] using hqm
  · simpa only [meaning] using hwm
  · rw [hbc,eb];exact hmodelBytes
#print axioms complete
end R1Z.PV_RunJoin_TailDecoderModel50
