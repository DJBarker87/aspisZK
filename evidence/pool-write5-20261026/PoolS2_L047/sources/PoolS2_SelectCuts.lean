import PoolS2_Prefix
set_option autoImplicit false
namespace AspisR1.PoolS2_SelectCuts
open Aeneas Aeneas.Std Result PoolS2_Prefix PoolS2_PrefixSource

theorem accepted (accounts : Slice Account) (roles : Roles) (h : select accounts = ok roles) :
    Slice.index_usize accounts 0#usize = ok roles.master ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Account)
      accounts {start := 1#usize, «end» := 9#usize} = ok roles.lanes ∧
    Slice.index_usize accounts 9#usize = ok roles.checkpoint ∧
    Slice.index_usize accounts 10#usize = ok roles.payer ∧
    Slice.index_usize accounts 11#usize = ok roles.system := by
  unfold select at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals aesop

#print axioms accepted
end AspisR1.PoolS2_SelectCuts
