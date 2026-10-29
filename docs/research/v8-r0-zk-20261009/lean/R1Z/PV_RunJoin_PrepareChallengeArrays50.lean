import R1Z.PV_RunJoin_PrepareProducedArrays50
import R1Z.PV_RunJoin_PrepareChallengeFields50
import R1Z.PV_RunJoin_PrepareTailSuccess48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareChallengeArrays50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitWideOps48
open PV_B2_F_ConstructorCarrier (Weight toWeight amap)
open PV_RunJoin_SemanticMaterialInputs50
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_CoefficientActualCell50 (Column)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend) (sem : Sem)
    (length : backend.messages.length=29) (out : prover.PreparedOpening)
    (h : @prover.prepare_opening (types base)
      (selected base heap box (@PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)))
      .S2 hash backend sem=ok (.Ok out)) :
    ∃ (coeff : alloc.vec.Vec Column) (qs ws : Array Source 1024#usize) (g k a : Raw)
      (bg bk ba : Array U8 32#usize) (hlen : coeff.length=29),
      canonical g ∧ canonical k ∧ canonical a ∧
      out.gamma=fromW (source g) ∧ out.kappa=fromW (source k) ∧ out.alpha0=fromW (source a) ∧
      value g=PhaseSamplerParserBin.openingScalar 0 (PV_RunJoin_OpeningBlock50.answer bg) ∧
      value k=PhaseSamplerParserBin.openingScalar 1 (PV_RunJoin_OpeningBlock50.answer bk) ∧
      value a=PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer ba) ∧
      ProverCommitGammaOutput53.run (PV_RunJoin_GammaActualInputs50.table (alloc.vec.Vec.deref coeff) hlen) (source g)=ok qs ∧
      ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize (alpha sem))
        (ProverCommitNativeQ48.source (x0 sem)) (ProverCommitNativeQ48.source (y0 sem))
        (ProverCommitNativeQ48.source (x1 sem)) (ProverCommitNativeQ48.source (y1 sem)) (source k)=ok ws := by
  let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
  obtain ⟨coeff,kw,qs,ws,tr,claim,gamma,inactive,kappa,hlen,himage,hq,hw,hbox,hheap,htail⟩ :=
    PV_RunJoin_PrepareProducedArrays50.complete base heap box ops hash backend sem length out h
  obtain ⟨g,k,a,bg,bk,ba,hcg,hck,hca,hgout,hkout,haout,hgv,hkv,hav⟩ :=
    PV_RunJoin_PrepareChallengeFields50.complete base heap box incoming .S2 hash backend sem out h
  obtain ⟨c0,bytes,actualAlpha,next,q1,w1,folded,hr,he,hs,hfq,hfw,hd,hfields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete base heap box incoming .S2 hash backend sem tr claim gamma inactive kappa
      (Array.to_slice (amap fromW qs)) (Array.to_slice (amap fromW ws)) out htail
  rcases hfields with ⟨hb,hm,ht,hy,hgamma,hi,hkappa,halpha,hbc,hqo,hwo,hfo⟩
  have eg : gamma=fromW (source g) := hgamma.symm.trans hgout
  have ek : kappa=fromW (source k) := hkappa.symm.trans hkout
  rw [eg,ProverRwDictionaryTower.native_w_roundtrip] at hq
  rw [ek,ProverRwDictionaryTower.native_w_roundtrip] at hw
  exact ⟨coeff,qs,ws,g,k,a,bg,bk,ba,hlen,hcg,hck,hca,hgout,hkout,haout,hgv,hkv,hav,hq,hw⟩
#print axioms complete
end R1Z.PV_RunJoin_PrepareChallengeArrays50
