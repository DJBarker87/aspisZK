import R1Z.PV_RunJoin_PrepareReach50
import R1Z.PV_RunJoin_CoefficientsActual50
import R1Z.PV_RunJoin_GammaArraySuccess50
import R1Z.PV_RunJoin_SemanticMaterialSuccess50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareProducedArrays50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight amap)
open PV_RunJoin_SemanticMaterialInputs50
open ProverRwDictionaryTower (fromW toW)
open PV_RunJoin_CoefficientActualCell50 (Column permuted)
abbrev S := ProverCommitWideOps48.Source
abbrev W := aspis_core.field.wide_exact.WideExact
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (backend : prover.Backend) (sem : Sem)
    (length : backend.messages.length=29) (out : prover.PreparedOpening)
    (h : @prover.prepare_opening (types base)
      (selected base heap box (@PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)))
      .S2 hash backend sem=ok (.Ok out)) :
    let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
    ∃ (coeff : alloc.vec.Vec Column) (kw : Weight) (qSource wSource : Array S 1024#usize)
      (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (claim : alloc.vec.Vec U8) (gamma inactive kappa : W) (hlen : coeff.length=29),
      coeff.val=backend.messages.val.map permuted ∧
      ProverCommitGammaOutput53.run (PV_RunJoin_GammaActualInputs50.table (alloc.vec.Vec.deref coeff) hlen) (toW gamma)=ok qSource ∧
      ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize (alpha sem))
        (ProverCommitNativeQ48.source (x0 sem)) (ProverCommitNativeQ48.source (y0 sem))
        (ProverCommitNativeQ48.source (x1 sem)) (ProverCommitNativeQ48.source (y1 sem)) (toW kappa)=ok wSource ∧
      box .S2 sem.alpha sem.z=ok () ∧ heap (toWeight kw) kappa=ok .supplied ∧
      @PV_RunJoin_PrepareTail48.run (types base) (selected base heap box incoming) .S2 hash backend sem
        tr claim gamma inactive kappa (Array.to_slice (amap fromW qSource))
          (Array.to_slice (amap fromW wSource))=ok (.Ok out) := by
  dsimp only
  let incoming := @PV_DL_EncoderSelected.selected (types base) (@PV_RunJoin_GammaPowers44.inputs (types base) ops)
  obtain ⟨coeff,scp,x,y,weight,tr0,tr1,tr2,claim,gamma,inactive,kappa,ib,q,w,
    hcoeff,hpoint,hx,hy,hclaim,hq,hctor,hi,hib,hmat,hg,hk,htail⟩ :=
    PV_RunJoin_PrepareReach50.complete base heap box incoming .S2 hash backend sem out h
  obtain ⟨produced,hproduced,hv,hl⟩ := PV_RunJoin_CoefficientsActual50.complete base heap box incoming
    (alloc.vec.Vec.deref backend.messages) (by change backend.messages.length≤14336;rw [length];omega)
  have eq : coeff=produced := Result.ok.inj (hcoeff.symm.trans hproduced)
  have hlen : coeff.length=29 := by rw [eq,hl];exact length
  have image : coeff.val=backend.messages.val.map permuted := by rw [eq];exact hv
  obtain ⟨qs,hqs,hqi,hql,hqimage⟩ := PV_RunJoin_GammaArraySuccess50.complete base heap box ops
    (alloc.vec.Vec.deref coeff) hlen gamma q hq
  obtain ⟨kw,ws,hbox,hweight,hheap,hws,hwi,hwl,hwimage⟩ :=
    PV_RunJoin_SemanticMaterialSuccess50.complete base heap box incoming sem weight kappa w hctor hmat
  refine ⟨coeff,kw,qs,ws,tr2,claim,gamma,inactive,kappa,hlen,image,hqs,hws,hbox,?_,?_⟩
  · rw [hweight];exact hheap
  · rw [←hqimage,←hwimage];exact htail
#print axioms complete
end R1Z.PV_RunJoin_PrepareProducedArrays50
