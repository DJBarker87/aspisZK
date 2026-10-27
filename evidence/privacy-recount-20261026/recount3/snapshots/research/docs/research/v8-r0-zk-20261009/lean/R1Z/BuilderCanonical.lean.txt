import R1Z.BuilderRefinement
import R1Z.BuilderSpendRelation
import R1J.SpendWitnessMap

/-! Canonical M31 witnesses and public inputs for the extracted composition.
The honest relation is Rspend⁺ on the embedded fields. In particular the
instance subtype contains no ModelRel, BuilderSoundOn or trace validity proof.
The shipped Rust records/public/glue identification remains a separate source
obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderCanonical
open R0P R0Z.ZkStatement R0Z.HonestValidity R0Z.BuilderModel R0Z.WriterRefine
open R1J.SpendWitnessMap R1Z.BuilderSpendRelation
open AspisR1.SpendRelation
variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Carry a semantic spend witness from M31 into K. -/
def liftWitness (w : Wspend) : Witness K where
  inputValue := w.inputValue
  outputValue := w.outputValue
  changeValue := w.changeValue
  sk := fun i => ι (w.sk i)
  salt := fun i => ι (w.salt i)
  path := fun l => ((w.path l).1, fun i => ι ((w.path l).2 i))
  pair := ⟨fun i => ι (w.pair.firstCommitment i), ι w.pair.secondOccupied,
    fun i => ι (w.pair.secondCommitment i), ι w.pair.secondOccupancyInverse⟩
  recipientOwner := fun i => ι (w.recipientOwner i)
  recipientSalt := fun i => ι (w.recipientSalt i)
  changeOwner := fun i => ι (w.changeOwner i)
  changeSalt := fun i => ι (w.changeSalt i)

theorem modelWitness_lift (w : Wspend) :
    modelWitness (liftWitness (K := K) w) = mapW (modelWitness w) := rfl

/-- Every M31 image belongs to every subfield of characteristic-p K. -/
theorem image_mem (F : Subfield K) (a : R1J.SpendWitnessMap.F) : ι a ∈ F := by
  rw [ι_apply]
  exact natCast_mem F _

theorem witnessBase_lift (F : Subfield K) (w : Wspend) :
    WitnessBase F (modelWitness (liftWitness w)) where
  sk := fun _ => image_mem F _
  salt := fun _ => image_mem F _
  path := fun _ _ => image_mem F _
  pairOccupied := image_mem F _
  pairSecond := fun _ => image_mem F _
  pairInverse := image_mem F _
  recipientOwner := fun _ => image_mem F _
  recipientSalt := fun _ => image_mem F _
  changeOwner := fun _ => image_mem F _
  changeSalt := fun _ => image_mem F _

theorem publicBase_map (F : Subfield K) (pub : Public R1J.SpendWitnessMap.F) :
    PublicBase F (mapPub pub) := by
  refine ⟨fun _ => image_mem F _, fun _ => image_mem F _, image_mem F _, ?_,
    fun _ => image_mem F _, ?_, fun _ _ => image_mem F _, fun _ => image_mem F _,
    fun _ _ => image_mem F _⟩
  · intro r hr i
    change pub.recipient.map (fun d i => (ι : R1J.SpendWitnessMap.F →+* K) (d i)) = some r at hr
    cases ho : pub.recipient with
    | none => simp only [ho, Option.map_none] at hr; contradiction
    | some d =>
      rw [ho, Option.map_some] at hr
      cases hr
      exact image_mem F _
  · intro a ha
    change pub.withdrawalAmount.map (ι : R1J.SpendWitnessMap.F →+* K) = some a at ha
    cases ho : pub.withdrawalAmount with
    | none => simp only [ho, Option.map_none] at ha; contradiction
    | some d =>
      rw [ho, Option.map_some] at ha
      cases ha
      exact image_mem F _

/-- Named canonical record maps; the words are exactly those of T1–T3. -/
def rustWitness (w : Wspend) : RustWitness := toRust (modelWitness w)
def rustPublic (pub : Public R1J.SpendWitnessMap.F) : RustPublic := toRustPub pub

/-- The lifted extracted trace is the semantic model on the embedded witness. -/
theorem canonical_trace (pub : Public R1J.SpendWitnessMap.F) (w : Wspend) :
    BuilderRefinement.mergedTrace (rustWitness w) (rustPublic pub) =
      buildModel (mapPub (K := K) pub) (modelWitness (liftWitness w)) := by
  rw [BuilderRefinement.mergedTrace_eq_model (rustWitness w) (rustPublic pub) (mapPub pub)
    (pubCorr_toRustPub pub) (witnessOk_toRust (modelWitness w))]
  rw [rustWitness, toModel_toRust, ← modelWitness_lift]

/-- No semantic model premise is assumed: it is derived from Rspend⁺. -/
theorem admitted_of_spend (F : Subfield K) (pub : Public R1J.SpendWitnessMap.F)
    (w : Wspend) (h : RspendPlus (mapPub pub) (liftWitness (K := K) w)) :
    BuilderRefinement.Admitted F (mapPub pub) (rustWitness w) (rustPublic pub) where
  publicCorr := pubCorr_toRustPub pub
  words := witnessOk_toRust (modelWitness w)
  semantic := by
    rw [rustWitness, toModel_toRust, ← modelWitness_lift]
    exact modelRel_of_spend F _ _ (publicBase_map F pub) (witnessBase_lift F w) h

/-- Mathematical honest instances of the embedded Rspend⁺ relation. -/
def Instance : Type :=
  {p : Public R1J.SpendWitnessMap.F × Wspend //
    RspendPlus (mapPub (K := K) p.1) (liftWitness p.2)}

/-- The builder is the extracted merged writer composition on canonical records. -/
def prover (π : Fin 1024 ≃ Fin 1024) : HonestProver K where
  Instance := Instance (K := K)
  transport := π
  «public» := fun p => mapPub p.val.1
  build := fun p => BuilderRefinement.mergedTrace (rustWitness p.val.2) (rustPublic p.val.1)

/-- All four BuilderSoundOn fields for canonical Rspend⁺ instances, with no
ModelRel, base-typing, lane, or helper hypothesis. -/
theorem builderSoundOn (hcard : 4096 < Fintype.card K) (F : Subfield K)
    (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (x : Statement K CommitHandle) :
    BuilderSoundOn (prover π) B x := by
  intro p hp
  change mapPub p.val.1 = x.1 at hp
  change HonestBuilderSound F x.1 B
    (BuilderRefinement.mergedTrace (rustWitness p.val.2) (rustPublic p.val.1))
  rw [← hp]
  exact BuilderRefinement.sound_merged hcard F B _ _ _
    (admitted_of_spend F p.val.1 p.val.2 p.property)

#print axioms modelWitness_lift
#print axioms image_mem
#print axioms witnessBase_lift
#print axioms publicBase_map
#print axioms canonical_trace
#print axioms admitted_of_spend
#print axioms builderSoundOn
end R1Z.BuilderCanonical
