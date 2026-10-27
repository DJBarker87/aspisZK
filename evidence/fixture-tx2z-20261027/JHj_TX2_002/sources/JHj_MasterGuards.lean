import JHi_AuthenticationPrefix
import JHg_AccountValues
import JHd_ReferenceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_MasterGuards
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open JHg_World
attribute [local irreducible] e2 JHg_DataMaster.value

theorem pool : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.master.identity.pool (e2.snapshot 1 384 384).key=ok false := by
  rfl
#print axioms pool

theorem mask (base : Ops) : (JHd_ReferenceSlots.install base).op16=ok 255#u8 := rfl
#print axioms mask

theorem mask_matches : (JHg_AccountValues.master.initialized_lane_mask !=255#u8)=false := rfl
#print axioms mask_matches
end AspisR1.JHj_MasterGuards
end
