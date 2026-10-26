import R0Z.BuilderModelRefines
import R0Z.BuilderWitnessMerged

/-! The four privacy builder fields for the extracted merged writer composition.

The trace here is the lifted output of `copyCellMerged`, not `buildModelSpec`.
`Admitted` makes the remaining caller obligations explicit: public/record
correspondence, word ranges, and the semantic model relation. It is NOT a
claim that the shipped compile functions imply those obligations. In particular
neither the generated Rust glue nor the compile entry points are extracted by
this module. See BUILDER-REFINEMENT-20261021.md for that boundary. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderRefinement
open R0P R0Z.ZkStatement R0Z.HonestValidity R0Z.BuilderComplete
open R0Z.BuilderModel R0Z.WriterRefine R0Z.BuilderSound

variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 0x7fffffff]

/-- The actual extracted merged writer output, with stage-H columns zero. -/
def mergedTrace (W : RustWitness) (P : RustPublic) : Trace K :=
  fun c r => liftU (copyCellMerged W P c r)

/-- Caller obligations, not a replacement definition of the deployed relation. -/
structure Admitted (F : Subfield K) (pub : Public K) (W : RustWitness) (P : RustPublic) : Prop where
  publicCorr : PubCorr P pub
  words : WitnessOk W
  semantic : ModelRel F pub (toModel W)

/-- A relation instance retaining the public input and the exact Rust records. -/
structure Instance (F : Subfield K) where
  pub : Public K
  witness : RustWitness
  rustPublic : RustPublic
  admitted : Admitted F pub witness rustPublic

/-- The prover model builds the extracted output directly. Transport is explicit. -/
def prover (F : Subfield K) (π : Fin 1024 ≃ Fin 1024) : HonestProver K where
  Instance := Instance F
  transport := π
  «public» := fun w => w.pub
  build := fun w => mergedTrace w.witness w.rustPublic

theorem mergedTrace_eq_model (W : RustWitness) (P : RustPublic) (pub : Public K)
    (hP : PubCorr P pub) (hW : WitnessOk W) :
    mergedTrace W P = buildModel pub (toModel W) := by
  funext c r
  exact (builder_witness_merged W P pub hP hW).2.2.2.2.2 c r

/-- All four fields for the extracted output. No field is assumed in `Admitted`. -/
theorem sound_merged (hcard : 4096 < Fintype.card K) (F : Subfield K)
    (B : PackBasis F) (pub : Public K) (W : RustWitness) (P : RustPublic)
    (h : Admitted F pub W P) : HonestBuilderSound F pub B (mergedTrace W P) := by
  rw [mergedTrace_eq_model W P pub h.publicCorr h.words]
  have hc := builderCore_of_refines hcard (buildModelSpec F) (ModelRel F)
    (builderRefines_model F) B pub h.semantic.pubBase (toModel W) h.semantic
  rw [buildModelSpec_build F pub (toModel W) h.semantic.pubBase h.semantic.witBase] at hc
  exact honestBuilderSound_of_core pub B _ hc

/-- The D46/D51 premise is now discharged for the extracted composition on
`Admitted` inputs, for every public fibre (including an empty fibre). -/
theorem builderSoundOn (hcard : 4096 < Fintype.card K) (F : Subfield K)
    (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn (prover F π) B x := by
  intro w hw
  change w.pub = x.1 at hw
  change HonestBuilderSound F x.1 B (mergedTrace w.witness w.rustPublic)
  rw [← hw]
  exact sound_merged hcard F B w.pub w.witness w.rustPublic w.admitted

theorem prover_public (F : Subfield K) (π : Fin 1024 ≃ Fin 1024) (w : Instance F) :
    (prover F π).public w = w.pub := rfl

theorem prover_build (F : Subfield K) (π : Fin 1024 ≃ Fin 1024) (w : Instance F) :
    (prover F π).build w = mergedTrace w.witness w.rustPublic := rfl

theorem prover_transport (F : Subfield K) (π : Fin 1024 ≃ Fin 1024) :
    (prover F π).transport = π := rfl

#print axioms mergedTrace_eq_model
#print axioms sound_merged
#print axioms builderSoundOn
#print axioms prover_public
#print axioms prover_build
#print axioms prover_transport
end R1Z.BuilderRefinement
