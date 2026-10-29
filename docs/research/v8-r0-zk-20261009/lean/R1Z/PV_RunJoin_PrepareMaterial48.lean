import R1Z.PV_RunJoin_PrepareMaterialContext47
import R1Z.PV_RunJoin_OpeningConstructor48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareMaterial48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_CoefficientsWeight46 (W Column messages payload)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (p : Nat → Nat → PV_RunJoin_CoefficientsWeight46.W) (hinput : alloc.vec.Vec.deref backend.messages=messages p) :
    ∃ coefficients : alloc.vec.Vec Column, ∃ kw : Weight, ∃ z0 z1 : Point,
      (toWeight kw).variant=.S2 ∧
      coefficients.val=payload p 0 29 ∧ coefficients.length=29 ∧
      AspisR1ProducerRelease47.weights53.new
        (amap PV_RunJoin_WeightKernel46.toQ (amap fromQ sem.alpha))
        (PV_RunJoin_WeightKernel46.toQ z0.x) (PV_RunJoin_WeightKernel46.toQ z0.y)
        (PV_RunJoin_WeightKernel46.toQ z1.x) (PV_RunJoin_WeightKernel46.toQ z1.y)=
          ok (PV_RunJoin_WeightCarrier46.state (toWeight kw)) ∧
      @prover.prepare_opening (types base) (selected base heap box ops) .S2 hash backend sem=
        @PV_RunJoin_PrepareOperations47.run (types base) (selected base heap box ops)
          .S2 hash backend sem (ok coefficients)
          (do let _ ← box .S2 sem.alpha sem.z;ok (.Ok (toWeight kw)))
          (fun _ x => mapResult PV_RunJoin_WeightMaterialInstalled47.nativeRust
            (PV_RunJoin_WeightMaterialResult47.run (heap (toWeight kw) x) (toWeight kw)
              (PV_B2_F_MaterializeNative.fromNative x))) := by
  obtain ⟨coefficients,hc,hv,hl⟩ := PV_RunJoin_CoefficientsInstalled46.complete base heap box ops p
  obtain ⟨kw,z0,z1,hs,_,_,hn,hm,_,hmat⟩ :=
    PV_RunJoin_OpeningConstructor48.complete base heap box ops sem.alpha sem.z
  refine ⟨coefficients,kw,z0,z1,hs,hv,hl,hm,?_⟩
  trans @PV_RunJoin_PrepareOperations47.run (types base) (selected base heap box ops)
    .S2 hash backend sem (ok coefficients)
    (do let _ ← box .S2 sem.alpha sem.z;ok (.Ok (toWeight kw)))
    (@weights.Weights.materialize (types base) (selected base heap box ops))
  · rw [@PV_RunJoin_PrepareOperations47.source (types base) (selected base heap box ops) .S2 hash backend sem,
      hinput,hc]
    exact congrArg (fun r => @PV_RunJoin_PrepareOperations47.run (types base) (selected base heap box ops)
      .S2 hash backend sem (ok coefficients) r
      (@weights.Weights.materialize (types base) (selected base heap box ops))) hn
  · apply @PV_RunJoin_PrepareMaterialContext47.complete (types base) (selected base heap box ops)
      .S2 hash backend sem (ok coefficients) (box .S2 sem.alpha sem.z) (toWeight kw)
    exact hmat
#print axioms complete
end R1Z.PV_RunJoin_PrepareMaterial48
