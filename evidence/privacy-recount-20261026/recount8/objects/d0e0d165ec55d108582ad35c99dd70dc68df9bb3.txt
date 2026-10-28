import R1Z.PV_RunJoin_WeightBox46
import R1Z.PV_RunJoin_WeightRows46
import R1Z.PV_RunJoin_WeightStored46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightObject46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)

theorem complete (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) :
    ∃ p a8 a9 f,
      let kw : Weight := {variant := .S2, factors := f, points := p, extra := Array.make 2#usize [a8,a9]}
      let w := toWeight kw
      @ProverRwFull.ExternalFuns.op252 (types base) (selected base heap box ops) .S2 alpha z=
        (do let _ ← box .S2 alpha z;ok (.Ok w)) ∧
      PV_RunJoin_WeightCarrier46.state w=PV_RunJoin_WeightStored46.kernelState kw ∧
      (∀ kind j : Usize, kind.val<7 →
        @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j=
          mapResult PV_RunJoin_WeightRawInstalled46.nativeQ
            (AspisR1ProducerRelease47.weights53.raw (PV_RunJoin_WeightCarrier46.state w) kind j)) ∧
      (∀ kappa,
        @ProverRwFull.ExternalFuns.op251 (types base) (selected base heap box ops) w kappa=
          PV_B2_F_ResourceFamilies.heapOriginal heap w kappa) := by
  obtain ⟨p,a8,a9,f,_,_,_,_,hc⟩ := PV_RunJoin_WeightBox46.complete base heap box ops alpha z
  refine ⟨p,a8,a9,f,hc,PV_RunJoin_WeightStored46.complete _,?_,?_⟩
  · intro kind j hk
    exact PV_RunJoin_WeightRows46.complete base heap box ops _ rfl kind j hk
  · intro kappa
    rw [PV_RunJoin_WeightInstalled46.materialize]
#print axioms complete
end R1Z.PV_RunJoin_WeightObject46
