import R1Z.PV_RunJoin_PrepareTailReach49
import R1Z.PV_RunJoin_PrepareTailSuccess48
import R1Z.PV_RunJoin_ScalarSuccessModel50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareChallengeFields50
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
    ∃ (g k a : Raw) (bg bk ba : Array U8 32#usize),
      canonical g ∧ canonical k ∧ canonical a ∧
      out.gamma=ProverRwDictionaryTower.fromW (source g) ∧
      out.kappa=ProverRwDictionaryTower.fromW (source k) ∧
      out.alpha0=ProverRwDictionaryTower.fromW (source a) ∧
      value g=PhaseSamplerParserBin.openingScalar 0 (PV_RunJoin_OpeningBlock50.answer bg) ∧
      value k=PhaseSamplerParserBin.openingScalar 1 (PV_RunJoin_OpeningBlock50.answer bk) ∧
      value a=PhaseSamplerParserBin.openingScalar 2 (PV_RunJoin_OpeningBlock50.answer ba) := by
  obtain ⟨tr0,tr1,tr2,claim,gamma,inactive,kappa,ib,q,w,hg,hk,htail⟩ :=
    PV_RunJoin_PrepareTailReach49.complete base heap box ops variant hash backend sem out h
  obtain ⟨bg,g,hbg,hcg,eg,hgv⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr0 0 27#u8 (alloc.vec.Vec.deref claim) gamma tr1 hg
  obtain ⟨bk,k,hbk,hck,ek,hkv⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr1 1 28#u8 (Array.to_slice ib) kappa tr2 hk
  obtain ⟨c0,bytes,actualAlpha,next,q1,w1,folded,hr,he,ha,hfq,hfw,hd,hfields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete base heap box ops variant hash backend sem tr2 claim gamma inactive kappa
      (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref w) out htail
  obtain ⟨ba,a,hba,hca,ea,hav⟩ := PV_RunJoin_ScalarSuccessModel50.complete base heap box ops _
    tr2 2 29#u8 (alloc.vec.Vec.deref bytes) actualAlpha next ha
  rcases hfields with ⟨hb,hm,ht,hy,hgamma,hi,hkappa,halpha,hbc,hqo,hwo,hfo⟩
  exact ⟨g,k,a,bg,bk,ba,hcg,hck,hca,hgamma.trans eg,hkappa.trans ek,halpha.trans ea,hgv,hkv,hav⟩
#print axioms complete
end R1Z.PV_RunJoin_PrepareChallengeFields50
