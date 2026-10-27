import RPv_JGa_WeightShift
import RPv_JFy_Steps
import RPv_JGa_LinkBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_LinkWeightBits
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_copy_terminal

theorem keep (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=4#u8) (hl : l.weight_level.val<64) :
    ∃ w,link_weight l index v=ok w := by
  obtain ⟨shift,hs⟩ := JGa_WeightShift.shift index l.weight_level hl
  refine ⟨JGa_WeightShift.bit shift,?_⟩
  unfold link_weight
  rw [hk]
  change (do let i ← index>>>l.weight_level;ok (JGa_WeightShift.bit i))=ok (JGa_WeightShift.bit shift)
  rw [hs,bind_tc_ok]
#print axioms keep

theorem complement (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=3#u8) (hl : l.weight_level.val<64) :
    ∃ w,link_weight l index v=ok w := by
  obtain ⟨shift,hs⟩ := JGa_WeightShift.shift index l.weight_level hl
  have hb := JGa_WeightShift.bound shift
  obtain ⟨w,hw,_⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=1#u32) (y:=JGa_WeightShift.bit shift) (by scalar_tac))
  refine ⟨w,?_⟩
  unfold link_weight
  rw [hk]
  change (do let i ← index>>>l.weight_level;let w ← 1#u32-JGa_WeightShift.bit i;ok w)=ok w
  rw [hs,bind_tc_ok,hw,bind_tc_ok]
#print axioms complement
end AspisR1.JGa_LinkWeightBits
end
