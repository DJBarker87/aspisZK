import R1Z.PV_RunJoin_WeightNew47
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightNewVariant47
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (K Point Weight)

theorem complete (alpha : Array K 10#usize) (z : Array Point 2#usize) (w : Weight)
    (hw : PV_B2_C_WeightsNative.host_weights.Weights.new .S2 alpha z=ok (.Ok w)) :
    w.variant=.S2 := by
  obtain ⟨p,a8,a9,f,_,_,_,_,hn⟩ := PV_RunJoin_WeightConstructorShape46.complete .S2 alpha z
  rw [hw] at hn
  have he := core.result.Result.Ok.inj (Result.ok.inj hn)
  exact congrArg (fun v : Weight => v.variant) he
#print axioms complete
end R1Z.PV_RunJoin_WeightNewVariant47
