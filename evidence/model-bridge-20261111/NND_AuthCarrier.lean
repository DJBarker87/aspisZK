import NND_LiveCarrier
set_option autoImplicit false
namespace NND_Carrier
def auth (x : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts) : RSL.Authenticated :=
 { master_account := key x.master_account,
   checkpoint_account := key x.checkpoint_account,
   selected_lane_account := key x.selected_lane_account,
   master := master x.master,
   checkpoint := checkpoint x.checkpoint,
   selected_lane := lane x.selected_lane,
   live_snapshot := live x.live_snapshot }
theorem auth_injective : Function.Injective auth := by
 intro x y h
 cases x
 cases y
 simp only [auth,RSL.Authenticated.mk.injEq,checkpoint_eq_iff,key_eq_iff,lane_eq_iff,live_eq_iff,master_eq_iff] at h
 exact AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts.mk.injEq.mpr h
@[simp] theorem auth_eq_iff (x y : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts) : auth x = auth y ↔ x = y :=
 ⟨fun h => auth_injective h,congrArg auth⟩
#print axioms auth_injective
#print axioms auth_eq_iff
end NND_Carrier
