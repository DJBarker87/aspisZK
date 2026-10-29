import R1Z.PV_RunJoin_PrepareMaterial48
import R1Z.PV_RunJoin_PreparePrefix48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaims48
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
        @PV_RunJoin_PrepareClaimContext48.run (types base) (selected base heap box ops)
          .S2 hash backend sem (ok coefficients)
          (do let _ ← box .S2 sem.alpha sem.z;ok (.Ok (toWeight kw)))
          (fun _ x => mapResult PV_RunJoin_WeightMaterialInstalled47.nativeRust
            (PV_RunJoin_WeightMaterialResult47.run (heap (toWeight kw) x) (toWeight kw)
              (PV_B2_F_MaterializeNative.fromNative x)))
          (fun columns point => PV_RunJoin_ClaimProducer48.run
            (PV_RunJoin_ClaimProducerCell48.evaluate base heap box ops point) columns.val (alloc.vec.Vec.new U8))
          (fun q _ => mapResult ProverRwDictionaryTower.fromW
            (PV_RunJoin_InactiveFinite48.run 1024 q (PV_RunJoin_WeightCarrier46.state (toWeight kw))
              AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO 0#usize)) := by
  obtain ⟨coefficients,kw,z0,z1,hs,hv,hl,hm,hr⟩ :=
    PV_RunJoin_PrepareMaterial48.complete base heap box ops hash backend sem p hinput
  refine ⟨coefficients,kw,z0,z1,hs,hv,hl,hm,?_⟩
  rw [hr]
  exact PV_RunJoin_PreparePrefix48.complete base heap box ops hash backend sem coefficients
    (by rw [hl];decide) (box .S2 sem.alpha sem.z) (toWeight kw) hs _
#print axioms complete
end R1Z.PV_RunJoin_PrepareClaims48
