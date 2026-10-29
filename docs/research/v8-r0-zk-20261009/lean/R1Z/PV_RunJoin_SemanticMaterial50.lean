import R1Z.PV_RunJoin_SemanticMaterialInputs50
import R1Z.PV_RunJoin_MaterialProducer49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticMaterial50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open PV_RunJoin_SemanticMaterialInputs50

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (s : Sem) :
    ∃ kw : Weight,
      (toWeight kw).variant=.S2 ∧
      @ExternalFuns.op252 (types base) (selected base heap box ops) .S2 s.alpha s.z=
        (do let _ ← box .S2 s.alpha s.z;ok (.Ok (toWeight kw))) ∧
      (∀ x : PV_RunJoin_MaterialVec49.S,
        @ExternalFuns.op251 (types base) (selected base heap box ops) (toWeight kw) (ProverRwDictionaryTower.fromW x)=
          PV_RunJoin_MaterialRun49.outcome (heap (toWeight kw) (ProverRwDictionaryTower.fromW x))
            (ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize (alpha s))
              (ProverCommitNativeQ48.source (x0 s)) (ProverCommitNativeQ48.source (y0 s))
              (ProverCommitNativeQ48.source (x1 s)) (ProverCommitNativeQ48.source (y1 s)) x)) := by
  obtain ⟨kw,hs,hctor,hmat⟩ := PV_RunJoin_MaterialProducer49.complete base heap box ops
    (alpha s) (x0 s) (y0 s) (x1 s) (y1 s)
  rw [alpha_eq,points_eq] at hctor
  exact ⟨kw,hs,hctor,hmat⟩
#print axioms complete
end R1Z.PV_RunJoin_SemanticMaterial50
