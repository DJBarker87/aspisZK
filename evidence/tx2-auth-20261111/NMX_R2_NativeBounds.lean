import NMX_R2_ArgsReify
set_option autoImplicit false
namespace NMX_R2_NativeBounds
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier
/-- Every physical/native-model argument already has the representation facts;
none is an extra protocol, history, child-result or caller success condition. -/
theorem account (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_AccountReify.Bounds (NMX_R2_Carrier.account a) := by
 constructor
 · intro n same
   cases h : a.length with
   | Err e => change reply (fun n : Usize => n.val) a.length = .ok n at same; rw [h] at same; cases same
   | Ok value =>
     change reply (fun n : Usize => n.val) a.length = .ok n at same
     rw [h] at same
     have eq := Except.ok.inj same
     rw [← eq]
     scalar_tac
 · intro b same
   cases h : a.bytes with
   | Err e => change reply (fun v => v.val.map byte) a.bytes = .ok b at same; rw [h] at same; cases same
   | Ok value =>
     change reply (fun v => v.val.map byte) a.bytes = .ok b at same
     rw [h] at same
     have eq := Except.ok.inj same
     rw [← eq,List.length_map]
     exact value.property

theorem args (a : NMX_RowSpec_233.Args) : NMX_R2_ArgsReify.Bounds (NMX_R2_CallArguments.auth a) := by
 constructor
 · simpa only [NMX_R2_CallArguments.auth,List.length_map] using a.accounts.property
 · intro x member
   obtain ⟨native,_,same⟩ := List.mem_map.mp member
   subst x
   exact account native
#print axioms account
#print axioms args
end NMX_R2_NativeBounds
