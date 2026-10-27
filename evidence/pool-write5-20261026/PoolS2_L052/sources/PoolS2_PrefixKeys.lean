import PoolS2_SelectCuts
import PoolS2_PrefixFacts
import PoolS2_Ranges
set_option autoImplicit false
namespace AspisR1.PoolS2_PrefixKeys
open Aeneas Aeneas.Std Result PoolS2_Prefix PoolS2_PrefixSource

theorem selected_key (accounts : Slice Account) (slot : Usize) (account : Account)
    (h : Slice.index_usize accounts slot = ok account) :
    ∃ within : slot.val < (keys accounts).val.length,
      ((keys accounts).val[slot.val]'within) = account.key := by
  obtain ⟨within,value⟩ := PoolS2_Ranges.indexed accounts slot account h
  have mapped : slot.val < (keys accounts).val.length := by simpa [keys] using within
  refine ⟨mapped,?_⟩
  simpa [keys,List.getElem_map] using congrArg (fun a : Account => a.key) value

theorem master_checkpoint (accounts : Slice Account) (data : Slice U8) (roles : Roles)
    (h : run accounts data = ok (.Ok roles)) : roles.checkpoint.key ≠ roles.master.key := by
  obtain ⟨_,_,distinct,chosen,_,_⟩ := PoolS2_PrefixFacts.accepted accounts data roles h
  have cuts := PoolS2_SelectCuts.accepted accounts roles chosen
  obtain ⟨hm,master⟩ := selected_key accounts 0#usize roles.master cuts.1
  obtain ⟨hc,checkpoint⟩ := selected_key accounts 9#usize roles.checkpoint cuts.2.2.1
  have different := PoolS2_UniqueRoles.ordered (keys accounts).val distinct 0 9 hm hc (by decide)
  intro same
  apply different
  rw [master,checkpoint,same]

#print axioms selected_key
#print axioms master_checkpoint
end AspisR1.PoolS2_PrefixKeys
