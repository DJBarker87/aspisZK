import R1Z.PV_RunJoin_PrepareTailSuccess48
import R1Z.PV_RunJoin_ScalarSuccess49
import R1Z.PV_RunJoin_FirstModel49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TailModelSuccess49
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
    ∃ (a q1 w1 c0 : Nat → Raw) (alpha : Raw) (hc0 : ∀ j,j<7 → canonical (c0 j)),
      canonical alpha ∧ out.alpha0=current (source alpha) ∧
      Array.to_slice (array 256#usize q1)=alloc.vec.Vec.deref out.q1 ∧
      Array.to_slice (array 256#usize w1)=alloc.vec.Vec.deref out.w1 ∧
      (∀ j,j<256 → canonical (q1 j) ∧ canonical (w1 j)) ∧
      (∀ i : Fin 256,value (q1 i.val)=AspisR1.RoundPairing.primalFold (value alpha)
        (fun j : Fin 1024 => value (q j.val)) i) ∧
      (∀ i : Fin 256,value (w1 i.val)=AspisR1.RoundPairing.dualFold (value alpha)
        (fun j : Fin 1024 => value (w j.val)) i) ∧
      out.c0bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hc0 := by
  obtain ⟨actualC0,actualBytes,actualAlpha,next,vq,vw,folded,hr,he,hs,hfq,hfw,hd,hfields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete base heap box ops variant hash backend sem tr y1 gamma inactive kappa
      (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w)) out h
  obtain ⟨block,alpha,hblock,hca,halpha,haval⟩ := PV_RunJoin_ScalarSuccess49.complete base heap box ops _
    tr 29#u8 (alloc.vec.Vec.deref actualBytes) false actualAlpha next hs
  obtain ⟨c0,q1,w1,vq1,vw1,bytes,hc0,hround,henc,hqfold,hwfold,hiq,hiw,hc,hqm,hwm,hbytes⟩ :=
    PV_RunJoin_FirstModel49.complete base heap box ops q w hq hw alpha hca
  have ec0 : actualC0=array 7#usize c0 := Result.ok.inj (hr.symm.trans hround)
  have ebytes : actualBytes=bytes := by
    rw [ec0] at he
    exact Result.ok.inj (he.symm.trans henc)
  rw [halpha] at hfq hfw
  have eqQ : vq=vq1 := Result.ok.inj (hfq.symm.trans hqfold)
  have eqW : vw=vw1 := Result.ok.inj (hfw.symm.trans hwfold)
  rcases hfields with ⟨hb,hm,ht,hy,hg,hi,hk,ha,hbc,hqout,hwout,hfo⟩
  refine ⟨q,q1,w1,c0,alpha,hc0,hca,ha.trans halpha,?_,?_,hc,hqm,hwm,?_⟩
  · rw [hqout,eqQ]
    exact hiq
  · rw [hwout,eqW]
    exact hiw
  · rw [hbc,ebytes]
    exact hbytes
#print axioms complete
end R1Z.PV_RunJoin_TailModelSuccess49
