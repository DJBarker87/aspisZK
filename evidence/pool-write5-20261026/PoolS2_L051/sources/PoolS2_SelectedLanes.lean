import PoolS2_SelectCuts
import PoolS2_PrefixFacts
import PoolS2_Ranges
set_option autoImplicit false
namespace AspisR1.PoolS2_SelectedLanes
open Aeneas Aeneas.Std Result PoolS2_Prefix PoolS2_PrefixSource

theorem selected (accounts : Slice Account) (roles : Roles) (count : accounts.val.length = 12)
    (h : select accounts = ok roles) :
    roles.lanes.val = (accounts.val.drop 1).take 8 ∧ roles.lanes.val.length = 8 := by
  have cuts := PoolS2_SelectCuts.accepted accounts roles h
  have range := PoolS2_Ranges.selected_exact accounts roles.lanes 1#usize 9#usize
    (by scalar_tac) (by change 9 ≤ accounts.val.length; omega) cuts.2.1
  exact range

theorem accepted (accounts : Slice Account) (data : Slice U8) (roles : Roles)
    (h : run accounts data = ok (.Ok roles)) :
    roles.lanes.val = (accounts.val.drop 1).take 8 ∧ roles.lanes.val.length = 8 := by
  obtain ⟨_,count,_,chosen,_,_⟩ := PoolS2_PrefixFacts.accepted accounts data roles h
  exact selected accounts roles count chosen

#print axioms selected
#print axioms accepted
end AspisR1.PoolS2_SelectedLanes
