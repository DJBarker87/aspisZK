import R1Z.PV_RunJoin_WeightNewVariant47
import R1Z.PV_RunJoin_WeightMaterialInstalled47
import R1Z.PV_RunJoin_WeightRows46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningConstructor48
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)

theorem complete (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) :
    ∃ kw : Weight, ∃ z0 z1 : Point,
      (toWeight kw).variant=.S2 ∧
      Array.index_usize (amap fromPoint z) 0#usize=ok z0 ∧
      Array.index_usize (amap fromPoint z) 1#usize=ok z1 ∧
      @ProverRwFull.ExternalFuns.op252 (types base) (selected base heap box ops) .S2 alpha z=
        (do let _ ← box .S2 alpha z;ok (.Ok (toWeight kw))) ∧
      AspisR1ProducerRelease47.weights53.new (amap PV_RunJoin_WeightKernel46.toQ (amap fromQ alpha))
        (PV_RunJoin_WeightKernel46.toQ z0.x) (PV_RunJoin_WeightKernel46.toQ z0.y)
        (PV_RunJoin_WeightKernel46.toQ z1.x) (PV_RunJoin_WeightKernel46.toQ z1.y)=
          ok (PV_RunJoin_WeightCarrier46.state (toWeight kw)) ∧
      (∀ kind j : Usize, kind.val<7 →
        @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) (toWeight kw) kind j=
          mapResult PV_RunJoin_WeightRawInstalled46.nativeQ
            (AspisR1ProducerRelease47.weights53.raw (PV_RunJoin_WeightCarrier46.state (toWeight kw)) kind j)) ∧
      (∀ x,
        @ProverRwFull.ExternalFuns.op251 (types base) (selected base heap box ops) (toWeight kw) x=
          mapResult PV_RunJoin_WeightMaterialInstalled47.nativeRust
            (PV_RunJoin_WeightMaterialResult47.run (heap (toWeight kw) x) (toWeight kw)
              (PV_B2_F_MaterializeNative.fromNative x))) := by
  obtain ⟨kw,z0,z1,h0,h1,hw,hm⟩ := PV_RunJoin_WeightNew47.complete (amap fromQ alpha) (amap fromPoint z)
  have hv := PV_RunJoin_WeightNewVariant47.complete _ _ kw hw
  have hs : (toWeight kw).variant=.S2 := by
    change to251Variant kw.variant=.S2
    rw [hv]
    rfl
  refine ⟨kw,z0,z1,hs,h0,h1,?_,?_,?_,?_⟩
  · rw [PV_RunJoin_WeightInstalled46.constructor]
    change PV_B2_F_ConstructorEffect.original (box .S2 alpha z) .S2 alpha z=_
    rw [←PV_B2_F_ConstructorEffect.complete_result]
    simp only [PV_B2_F_ConstructorEffect.copied,fromVariant,hw,bind_tc_ok,
      PV_B2_F_ConstructorEffect.finish]
  · rw [PV_RunJoin_WeightStored46.complete]
    exact hm
  · intro kind j hk
    exact PV_RunJoin_WeightRows46.complete base heap box ops _ hs kind j hk
  · intro x
    exact PV_RunJoin_WeightMaterialInstalled47.complete base heap box ops _ hs x
#print axioms complete
end R1Z.PV_RunJoin_OpeningConstructor48
