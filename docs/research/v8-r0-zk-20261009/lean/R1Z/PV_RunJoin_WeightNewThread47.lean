import R1Z.PV_RunJoin_WeightConstructorModelRows47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightNewThread47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K Point amap)
open PV_B2_C_ConstructorRows (Points)
open PV_RunJoin_WeightKernel46 (toQ)

theorem complete (alpha : Array K 10#usize) (p : Points) (z : Array Point 2#usize)
    (z0 z1 : Point)
    (hp : PV_B2_C_WeightsNative.host_weights.state_only_statement_points alpha=ok p)
    (h0 : Array.index_usize z 0#usize=ok z0) (h1 : Array.index_usize z 1#usize=ok z1) :
    AspisR1ProducerRelease47.weights53.new (amap toQ alpha)
      (toQ z0.x) (toQ z0.y) (toQ z1.x) (toQ z1.y)=(do
        let f ← PV_RunJoin_WeightConstructorModelRows47.run p z
        let a8 ← Array.index_usize (amap toQ alpha) 8#usize
        let a9 ← Array.index_usize (amap toQ alpha) 9#usize
        ok (2#u8,f,amap (amap toQ) p,Array.make 2#usize [a8,a9])) := by
  rw [AspisR1ProducerRelease47.weights53.new,PV_RunJoin_WeightPoints47.complete,hp]
  simp only [PV_B2_E_OrdinaryOriginal.mapResult,bind_tc_ok,
    PV_RunJoin_WeightConstructorModelRows47.run,h0,h1,bind_assoc]
#print axioms complete
end R1Z.PV_RunJoin_WeightNewThread47
