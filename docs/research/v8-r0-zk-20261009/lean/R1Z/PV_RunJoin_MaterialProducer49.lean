import R1Z.PV_RunJoin_MaterialNew49
import R1Z.PV_RunJoin_MaterialRun49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialProducer49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_RunJoin_MaterialInputs49 (alpha points)
open PV_RunJoin_MaterialVec49 (S)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (p : Nat → Old.Q) (x0 y0 x1 y1 : Old.Q) :
    ∃ kw : Weight,
      (toWeight kw).variant=.S2 ∧
      @ExternalFuns.op252 (types base) (selected base heap box ops) .S2 (alpha p) (points x0 y0 x1 y1)=
        (do let _ ← box .S2 (alpha p) (points x0 y0 x1 y1);ok (.Ok (toWeight kw))) ∧
      (∀ x : S,@ExternalFuns.op251 (types base) (selected base heap box ops) (toWeight kw)
          (ProverRwDictionaryTower.fromW x)=
        PV_RunJoin_MaterialRun49.outcome (heap (toWeight kw) (ProverRwDictionaryTower.fromW x))
          (ProverCommitWeightsMaterial53.run (ProverCommitQArray48.array 10#usize p)
            (ProverCommitNativeQ48.source x0) (ProverCommitNativeQ48.source y0)
            (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1) x)) := by
  obtain ⟨kw,hs,hctor,hnew,hmat⟩ := PV_RunJoin_MaterialNew49.complete base heap box ops p x0 y0 x1 y1
  refine ⟨kw,hs,hctor,?_⟩
  intro x
  rw [PV_RunJoin_MaterialRun49.complete base heap box ops _ hs]
  simp only [ProverCommitWeightsMaterial53.run,hnew,bind_tc_ok]
#print axioms complete
end R1Z.PV_RunJoin_MaterialProducer49
