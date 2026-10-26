import GSPointSamplerAllocationM10
import GSByteBankAllocationStageM10
import PostProcessAllocationM10
import AllocationStageCompositionLawsM10
import ComposedContinuationSpecM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.AllocatedContinuationM10
open AspisWideTower AspisV8R15.ExactTowerBase GSFixedInputDecoderFamily
open AspisPool.AlgorithmicCircleDecoderV7 GSPostProcessWorkM10
open AllocationStageSpecM10
attribute [local irreducible] GSPointBatchWorkM10.inputs GSByteBankWorkM10.run
  PostProcessAllocationM10.eval GSPostProcessCompleteM10.eval
  InitialPublicImageWorkM10.budget ComposedContinuationSpecM10.budget
  AspisWide.GSConcreteReceivedWordInputs.fromWords GSConcreteByteDecoderBank.run
  LiteralComputedCandidateExtract.extract GSByteJointSpendExtractor.decodedLists

def guard {A B : Type} {f : A → Option B} {I : A → Prop} {J : B → Prop}
    {F : Nat → Nat} (P : Prop) (s : StageSpec 1024 f I J F) :
    StageSpec 1024 f (fun a => I a ∧ P) (fun b => J b ∧ P) F where
  toStageSpec := StageGuardM10.guard P s.toStageSpec
  allocation := s.allocation

@[irreducible] def points : StageSpec 1024
    (fun w : PointStageSpecM10.WordPair => some (AspisWide.GSConcreteReceivedWordInputs.fromWords w.1 w.2))
    (fun _ => True) (fun _ => True) (fun _ => GSPointBatchWorkM10.budget) where
  toStageSpec := PointStageSpecM10.spec
  allocation w := ⟨GSPointSamplerAllocationM10.inputsCells w.1 w.2,
    1024*GSPointSamplerAllocationM10.inputsCells w.1 w.2,Nat.le_refl _,by
      simpa only [PointStageSpecM10.spec,AbstractStageSpecM10.pureStage] using
        GSPointSamplerAllocationM10.inputs_paid w.1 w.2⟩

@[irreducible] def post (pub : R0P.Public M31Exact) (W : Fin 29 → InitialWord WideExact) :
    StageSpec 1024
      (fun out : Results WideExact 5 => LiteralComputedCandidateExtract.extract pub W
        (GSByteJointSpendExtractor.decodedLists W out))
      (fun out => GSBankOutputEnvelopeM10.Bounded out ∧ pub.nextPairIndex < 2^64)
      (fun _ => True) (fun _ => GSPostProcessCompleteM10.budget InitialPublicImageWorkM10.budget) where
  run := PostProcessAllocationM10.eval pub W
  value out := by
    rw [PostProcessAllocationM10.erase]
    exact GSPostProcessCompleteM10.value _ _ _ _
  work _ out h := by
    rw [PostProcessAllocationM10.erase]
    exact GSPostProcessCompleteM10.work _ _ InitialPublicImageWorkM10.bounded pub h.2 W out h.1
  invariant _ _ _ _ := True.intro
  allocation out := ⟨PostProcessAllocationM10.cells pub W out,1024*PostProcessAllocationM10.cells pub W out,
    Nat.le_refl _,PostProcessAllocationM10.paid pub W out⟩

theorem post_erase (pub : R0P.Public M31Exact) (W : Fin 29 → InitialWord WideExact)
    (out : Results WideExact 5) :
    ((post pub W).run out) =
      (PostStageSpecM10.spec InitialPublicImageWorkM10.image InitialPublicImageWorkM10.budget
        InitialPublicImageWorkM10.bounded pub W).run out := by
  unfold post PostStageSpecM10.spec
  exact PostProcessAllocationM10.erase pub W out

/-- Equality of complete writer results, not just Option values. -/
theorem bind_congr {A B : Type} (x y : Option A × Nat)
    (f g : A → Option B × Nat) (h : x = y) (hf : ∀ a, f a = g a) :
    PublicParserWork.bind x f = PublicParserWork.bind y g := by
  cases h
  rw [funext hf]

@[irreducible] def spec (pub : R0P.Public M31Exact)
    (W : Fin 29 → InitialWord WideExact) (coins : GSConcreteByteDecoderBank.RawCoins) :=
  AllocationStageCompositionLawsM10.compose (guard (pub.nextPairIndex < 2^64) points)
    (AllocationStageCompositionLawsM10.compose
      (guard (pub.nextPairIndex < 2^64) (GSByteBankAllocationStageM10.spec coins)) (post pub W))

theorem value (pub : R0P.Public M31Exact)
    (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    ((spec pub W coins).run (W,V)).1 = GSByteJointSpendExtractor.extract pub W V coins :=
  ((spec pub W coins).value (W,V)).trans (ContinuationReferenceM10.value pub W V coins)

theorem work (pub : R0P.Public M31Exact) (hp : pub.nextPairIndex < 2^64)
    (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    ((spec pub W coins).run (W,V)).2 ≤ ComposedContinuationSpecM10.budget InitialPublicImageWorkM10.budget := by
  unfold ComposedContinuationSpecM10.budget
  exact (spec pub W coins).work 0 (W,V) ⟨True.intro,hp⟩

theorem paid (pub : R0P.Public M31Exact)
    (W : Fin 29 → InitialWord WideExact) (coins : GSConcreteByteDecoderBank.RawCoins)
    (w : PointStageSpecM10.WordPair) :
    ((spec pub W coins).allocation w).bits ≤ 1024*((spec pub W coins).run w).2 :=
  allocation_le_work (spec pub W coins) w

#print axioms post_erase
#print axioms bind_congr
#print axioms value
#print axioms work
#print axioms paid
end AspisR1.AllocatedContinuationM10
end
