import R1Z.PV_RunJoin_TranscriptHash51
import R1Z.PV_RunJoin_PrepareReach51
import R1Z.PV_RunJoin_PrepareTailSuccess48
import R1Z.PV_RunJoin_ScalarSuccessModel50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareChallengeBlocks51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (out : prover.PreparedOpening)
    (h : @prover.prepare_opening (types base) (selected base heap box ops) variant hash backend sem=ok (.Ok out)) :
    ∃ (tr0 tr1 tr2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (g k a : Raw) (bg bk ba ib : Array U8 32#usize),
      @host_transcript.Transcript.new (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        hash sem.transcript.state variant=ok tr0 ∧
      tr0.hash=hash ∧ tr1.hash=hash ∧ tr2.hash=hash ∧ out.transcript.hash=hash ∧
      canonical g ∧ canonical k ∧ canonical a ∧
      out.gamma=ProverRwDictionaryTower.fromW (source g) ∧
      out.kappa=ProverRwDictionaryTower.fromW (source k) ∧
      out.alpha0=ProverRwDictionaryTower.fromW (source a) ∧
      @aspis_core.field.wide_exact.WideExact.to_le_bytes (types base) (selected base heap box ops) out.inactive=ok ib ∧
      @host_transcript.Transcript.block _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        tr0 27#u8 (alloc.vec.Vec.deref out.y1)=ok (bg,tr1) ∧
      @host_transcript.Transcript.block _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        tr1 28#u8 (Array.to_slice ib)=ok (bk,tr2) ∧
      @host_transcript.Transcript.block _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        tr2 29#u8 (alloc.vec.Vec.deref out.c0bytes)=ok (ba,out.transcript) ∧
      value g=PhaseSamplerParserBin.openingScalar 0 (PV_RunJoin_OpeningBlock50.answer bg) ∧
      value k=PhaseSamplerParserBin.openingScalar 1 (PV_RunJoin_OpeningBlock50.answer bk) ∧
      value a=PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer ba) := by
  obtain ⟨coeff,scp,x,y,weight,tr0,tr1,tr2,claim,gamma,inactive,kappa,ib,q,w,
    hnew,hcoeff,hpoint,hx,hy,hclaim,hq,hctor,hi,hib,hmat,hg,hk,htail⟩ :=
    PV_RunJoin_PrepareReach51.complete base heap box ops variant hash backend sem out h
  obtain ⟨bg,g,hbg,hcg,eg,hgv⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr0 0 27#u8 (alloc.vec.Vec.deref claim) gamma tr1 hg
  obtain ⟨bk,k,hbk,hck,ek,hkv⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr1 1 28#u8 (Array.to_slice ib) kappa tr2 hk
  obtain ⟨c0,bytes,actualAlpha,next,q1,w1,folded,hr,he,ha,hfq,hfw,hd,hfields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete base heap box ops variant hash backend sem tr2 claim gamma inactive kappa
      (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref w) out htail
  obtain ⟨ba,a,hba,hca,ea,hav⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr2 2 29#u8 (alloc.vec.Vec.deref bytes) actualAlpha next ha
  rcases hfields with ⟨hb,hm,ht,hy,hgamma,hinactive,hkappa,halpha,hbc,hqo,hwo,hfo⟩
  have h0 := PV_RunJoin_TranscriptHash51.reseed base heap box ops hash sem.transcript.state variant tr0 hnew
  have h1 := (PV_RunJoin_TranscriptHash51.block _ tr0 tr1 _ _ bg hbg).trans h0
  have h2 := (PV_RunJoin_TranscriptHash51.block _ tr1 tr2 _ _ bk hbk).trans h1
  have h3 := (PV_RunJoin_TranscriptHash51.block _ tr2 next _ _ ba hba).trans h2
  have hout : out.transcript.hash=hash := by rw [ht];exact h3
  refine ⟨tr0,tr1,tr2,g,k,a,bg,bk,ba,ib,hnew,h0,h1,h2,hout,hcg,hck,hca,hgamma.trans eg,hkappa.trans ek,halpha.trans ea,?_,?_,hbk,?_,hgv,hkv,hav⟩
  · rw [hinactive];exact hib
  · rw [hy];exact hbg
  · rw [hbc,ht];exact hba
#print axioms complete
end R1Z.PV_RunJoin_PrepareChallengeBlocks51
