import R1Z.PV_RunJoin_WeightTensor46
import R1Z.PV_RunJoin_WeightResult46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRawTensor46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46

theorem source (w : W) (hs : w.variant=.S2) (kind j : Usize)
    (h0 : kind≠0#usize) (h4 : kind≠4#usize) :
    PV_B2_251c1.host_weights.raw_value w kind j=(do
      let k ← if kind<4#usize then ok (Usize.wrapping_sub kind 1#usize)
        else ok (Usize.wrapping_sub kind 2#usize)
      let rows ← Array.index_usize w.factors k
      PV_B2_251c1.host_weights.tensor_raw rows j) := by
  rw [PV_B2_F_RawOriginal.source]
  simp only [PV_B2_F_RawOriginal.original,h0,h4,hs,reduceCtorEq,and_false,
    if_false,PV_B2_F_RawOriginal.tensor,PV_B2_F_RawFold.tensor_source]
#print axioms source
end R1Z.PV_RunJoin_WeightRawTensor46
