import R1Z.PV_RunJoin_BoxSuccess50
import R1Z.PV_RunJoin_MaterialOutcomeSuccess50
import R1Z.PV_RunJoin_PrefixImage50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticMaterialSuccess50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight amap)
open PV_RunJoin_SemanticMaterialInputs50
open ProverRwDictionaryTower (fromW toW)
abbrev W := aspis_core.field.wide_exact.WideExact

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (s : Sem) (weight : @weights.Weights (types base)) (k : W) (out : alloc.vec.Vec W)
    (hnew : @weights.Weights.new (types base) (selected base heap box ops) .S2 s.alpha s.z=ok (.Ok weight))
    (hmat : @weights.Weights.materialize (types base) (selected base heap box ops) weight k=ok (.Ok out)) :
    ∃ (kw : Weight) (a : Array ProverCommitWideOps48.Source 1024#usize),
      box .S2 s.alpha s.z=ok () ∧ toWeight kw=weight ∧ heap weight k=ok .supplied ∧
      ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize (alpha s))
        (ProverCommitNativeQ48.source (x0 s)) (ProverCommitNativeQ48.source (y0 s))
        (ProverCommitNativeQ48.source (x1 s)) (ProverCommitNativeQ48.source (y1 s)) (toW k)=ok a ∧
      out=PV_RunJoin_PrefixFold50.image fromW a ∧ out.length=1024 ∧
      alloc.vec.Vec.deref out=Array.to_slice (amap fromW a) := by
  obtain ⟨kw,hs,hctor,hmaterial⟩ := PV_RunJoin_SemanticMaterial50.complete base heap box ops s
  change @ExternalFuns.op252 (types base) (selected base heap box ops) .S2 s.alpha s.z=ok (.Ok weight) at hnew
  rw [hctor] at hnew
  obtain ⟨hbox,he⟩ := PV_RunJoin_BoxSuccess50.complete _ (toWeight kw) weight hnew
  subst weight
  change @ExternalFuns.op251 (types base) (selected base heap box ops) (toWeight kw) k=ok (.Ok out) at hmat
  have hm := hmaterial (toW k)
  simp only [ProverRwDictionaryTower.w_roundtrip] at hm
  rw [hm] at hmat
  obtain ⟨hheap,a,hr,himage⟩ := PV_RunJoin_MaterialOutcomeSuccess50.complete _ _ _ hmat
  have native : out=PV_RunJoin_PrefixFold50.image fromW a := himage.symm.trans (PV_RunJoin_PrefixImage50.material a)
  refine ⟨kw,a,hbox,rfl,hheap,hr,native,?_,?_⟩
  · rw [native];exact PV_RunJoin_PrefixImage50.length _ _
  · rw [native];exact PV_RunJoin_PrefixImage50.slice _ _
#print axioms complete
end R1Z.PV_RunJoin_SemanticMaterialSuccess50
