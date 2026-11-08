import NMX_R8_SimulatesPath
import NMX_R8_Stops
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Indexes241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted

theorem full (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (i : Usize) :
 Simulates (fun a => Except.ok (NMS_R2N_RSLPoolCarriers.account a))
  (liftResult (Slice.index_usize accounts i))
  (RSL.RS.index (NMS_R2N_RSLPoolCarriers.accounts accounts) i.val) := by
 unfold Slice.index_usize RSL.RS.index
 rw [Slice.getElem?_Usize_eq]
 simp only [NMS_R2N_RSLPoolCarriers.accounts,List.getElem?_map]
 cases found : accounts.val[i.val]? with
 | some a =>
   simp only [Option.map_some]
   exact NMS_R2N_Interpreted.pure _ _
 | none =>
   simp only [Option.map_none]
   change Simulates _ RSL.Spec.panic (RSL.Spec.map Except.ok RSL.Spec.panic)
   unfold RSL.Spec.map
   rw [NMX_R8_Stops.panic_bind]
   intro env o run
   subst o
   rfl
#print axioms full
end NMX_R8_Indexes241
end
