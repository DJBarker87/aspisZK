import R1Z.PV_RunJoin_WeightNewThread47
import R1Z.PV_RunJoin_WeightStored46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightNew47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K Point Weight amap)
open PV_RunJoin_WeightKernel46 (toQ)

theorem complete (alpha : Array K 10#usize) (z : Array Point 2#usize) :
    ∃ w : Weight, ∃ z0 z1 : Point,
      Array.index_usize z 0#usize=ok z0 ∧ Array.index_usize z 1#usize=ok z1 ∧
      PV_B2_C_WeightsNative.host_weights.Weights.new .S2 alpha z=ok (.Ok w) ∧
      AspisR1ProducerRelease47.weights53.new (amap toQ alpha)
        (toQ z0.x) (toQ z0.y) (toQ z1.x) (toQ z1.y)=
          ok (PV_RunJoin_WeightStored46.kernelState w) := by
  obtain ⟨p,a8,a9,f,hp,h8,h9,hf,hw⟩ := PV_RunJoin_WeightConstructorShape46.complete .S2 alpha z
  obtain ⟨z0,h0⟩ := PV_B2_C_ArrayTotal.read z 0#usize (by decide)
  obtain ⟨z1,h1⟩ := PV_B2_C_ArrayTotal.read z 1#usize (by decide)
  rw [PV_RunJoin_WeightConstructorRows47.complete] at hf
  have hm : PV_RunJoin_WeightConstructorModelRows47.run p z=
      ok (amap (amap (amap toQ)) f) := by
    rw [PV_RunJoin_WeightConstructorModelRows47.complete,hf]
    rfl
  refine ⟨{variant:=.S2,factors:=f,points:=p,extra:=Array.make 2#usize [a8,a9]},z0,z1,h0,h1,hw,?_⟩
  rw [PV_RunJoin_WeightNewThread47.complete alpha p z z0 z1 hp h0 h1]
  simp only [hm,bind_tc_ok,PV_RunJoin_WeightMap46.index,h8,h9]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightNew47
