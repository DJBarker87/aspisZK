import RPv_JGa_LinkBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_LinkWeightSimple
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal

theorem zero (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=0#u8) :
    ∃ w,link_weight l index v=ok w := by
  unfold link_weight
  rw [hk]
  exact ⟨_,rfl⟩
#print axioms zero

theorem transfer (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=1#u8) :
    ∃ w,link_weight l index v=ok w := by
  unfold link_weight
  rw [hk]
  unfold PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
  simp only [bind_tc_ok,lift]
  exact ⟨_,rfl⟩
#print axioms transfer

theorem withdrawal (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=2#u8) :
    ∃ w,link_weight l index v=ok w := by
  unfold link_weight
  rw [hk]
  unfold PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
  simp only [bind_tc_ok,lift]
  exact ⟨_,rfl⟩
#print axioms withdrawal
end AspisR1.JGa_LinkWeightSimple
end
