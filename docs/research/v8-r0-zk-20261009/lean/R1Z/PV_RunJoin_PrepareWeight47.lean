import R1Z.PV_RunJoin_PrepareContext47
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareWeight47
open Aeneas Aeneas.Std Result ProverRwFull
open PV_B2_F_ConstructorCarrier
open PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend)
    (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
    ∃ kw : Weight, ∃ z0 z1 : Point,
      Array.index_usize (amap fromPoint sem.z) 0#usize=ok z0 ∧
      Array.index_usize (amap fromPoint sem.z) 1#usize=ok z1 ∧
      AspisR1ProducerRelease47.weights53.new
        (amap PV_RunJoin_WeightKernel46.toQ (amap fromQ sem.alpha))
        (PV_RunJoin_WeightKernel46.toQ z0.x) (PV_RunJoin_WeightKernel46.toQ z0.y)
        (PV_RunJoin_WeightKernel46.toQ z1.x) (PV_RunJoin_WeightKernel46.toQ z1.y)=
          ok (PV_RunJoin_WeightCarrier46.state (toWeight kw)) ∧
      @prover.prepare_opening (types base) (selected base heap box ops) .S2 hash backend sem=
        @PV_RunJoin_PrepareContext47.run (types base) (selected base heap box ops) .S2 hash backend sem
          (do let _ ← box .S2 sem.alpha sem.z;ok (.Ok (toWeight kw))) := by
  obtain ⟨kw,z0,z1,h0,h1,hn,hm,_,_⟩ :=
    PV_RunJoin_WeightConstructorInstalled47.complete base heap box ops sem.alpha sem.z
  refine ⟨kw,z0,z1,h0,h1,hm,?_⟩
  rw [@PV_RunJoin_PrepareContext47.source (types base) (selected base heap box ops) .S2 hash backend sem]
  rw [hn]
#print axioms complete
end R1Z.PV_RunJoin_PrepareWeight47
