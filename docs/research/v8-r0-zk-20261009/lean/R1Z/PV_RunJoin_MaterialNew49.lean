import R1Z.PV_RunJoin_MaterialInputs49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialNew49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (Weight toWeight)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_MaterialInputs49 (alpha points)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (p : Nat → Old.Q) (x0 y0 x1 y1 : Old.Q) :
    ∃ kw : Weight,
      (toWeight kw).variant=.S2 ∧
      @ExternalFuns.op252 (types base) (selected base heap box ops) .S2 (alpha p) (points x0 y0 x1 y1)=
        (do let _ ← box .S2 (alpha p) (points x0 y0 x1 y1);ok (.Ok (toWeight kw))) ∧
      AspisR1ProducerRelease47.weights53.new (ProverCommitQArray48.array 10#usize p)
        (ProverCommitNativeQ48.source x0) (ProverCommitNativeQ48.source y0)
        (ProverCommitNativeQ48.source x1) (ProverCommitNativeQ48.source y1)=
          ok (PV_RunJoin_WeightCarrier46.state (toWeight kw)) ∧
      (∀ x,@ExternalFuns.op251 (types base) (selected base heap box ops) (toWeight kw) x=
        mapResult PV_RunJoin_WeightMaterialInstalled47.nativeRust
          (PV_RunJoin_WeightMaterialResult47.run (heap (toWeight kw) x) (toWeight kw)
            (PV_B2_F_MaterializeNative.fromNative x))) := by
  obtain ⟨kw,z0,z1,hs,h0,h1,hctor,hnew,hraw,hmat⟩ :=
    PV_RunJoin_OpeningConstructor48.complete base heap box ops (alpha p) (points x0 y0 x1 y1)
  have e0 : z0=PV_B2_F_ConstructorCarrier.fromPoint (PV_RunJoin_MaterialInputs49.point x0 y0) :=
    Result.ok.inj (h0.symm.trans (PV_RunJoin_MaterialInputs49.read0 x0 y0 x1 y1))
  have e1 : z1=PV_B2_F_ConstructorCarrier.fromPoint (PV_RunJoin_MaterialInputs49.point x1 y1) :=
    Result.ok.inj (h1.symm.trans (PV_RunJoin_MaterialInputs49.read1 x0 y0 x1 y1))
  rw [e0,e1] at hnew
  simp only [PV_RunJoin_MaterialInputs49.alpha_model,PV_RunJoin_MaterialInputs49.x_model,
    PV_RunJoin_MaterialInputs49.y_model] at hnew
  exact ⟨kw,hs,hctor,hnew,hmat⟩
#print axioms complete
end R1Z.PV_RunJoin_MaterialNew49
