import R1Z.PV_RunJoin_WeightConstructorShape46
import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightBox46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier
open PV_RunJoin_WeightInstalled46

theorem complete (base : ProverRwFull.ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ProverRwFull.ExternalFuns (types base)) (alpha : Array NQ 10#usize)
    (z : Array NP 2#usize) :
    ∃ p a8 a9 f,
      PV_B2_C_WeightsNative.host_weights.state_only_statement_points (amap fromQ alpha)=ok p ∧
      Array.index_usize (amap fromQ alpha) 8#usize=ok a8 ∧
      Array.index_usize (amap fromQ alpha) 9#usize=ok a9 ∧
      PV_RunJoin_WeightConstructorThread46.rows p (amap fromPoint z)
        PV_RunJoin_WeightConstructorShape46.seed=ok f ∧
      @ProverRwFull.ExternalFuns.op252 (types base) (selected base heap box ops) .S2 alpha z=
        (do let _ ← box .S2 alpha z
            ok (.Ok (toWeight ({variant := .S2, factors := f, points := p, extra := Array.make 2#usize [a8,a9]} : Weight)))) := by
  obtain ⟨p,a8,a9,f,hp,h8,h9,hf,hn⟩ :=
    PV_RunJoin_WeightConstructorShape46.complete .S2 (amap fromQ alpha) (amap fromPoint z)
  refine ⟨p,a8,a9,f,hp,h8,h9,hf,?_⟩
  rw [PV_RunJoin_WeightInstalled46.constructor]
  change PV_B2_F_ConstructorEffect.original (box .S2 alpha z) .S2 alpha z=_
  rw [← PV_B2_F_ConstructorEffect.complete_result]
  simp only [PV_B2_F_ConstructorEffect.copied,fromVariant,hn,bind_tc_ok,
    PV_B2_F_ConstructorEffect.finish]
#print axioms complete
end R1Z.PV_RunJoin_WeightBox46
