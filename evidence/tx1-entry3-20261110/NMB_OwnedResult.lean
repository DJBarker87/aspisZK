import NMB_OwnedTyped
set_option autoImplicit false
noncomputable section
namespace NMB_OwnedResult
open Aeneas Aeneas.Std Result AspisR1 NMB_TypedTrace
/-- Full nominal Result erasure, not just accepted replies or occurrence IDs. -/
theorem source (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
 (NMB_OwnedTyped.stage1Owned ops program accounts data).result=
 AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data := by
 have h:=congrArg Prod.snd (NMB_OwnedTyped.forget_eq ops program accounts data)
 exact h.trans (NLD_Stage1Source.erasure ops program accounts data)
theorem occurrences (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
 ((NMB_OwnedTyped.stage1Owned ops program accounts data).events.map Event.site)=
 (NLD_Stage1Source.stage1Owned ops program accounts data).1 :=
 congrArg Prod.fst (NMB_OwnedTyped.forget_eq ops program accounts data)
#print source
#print axioms source
#print axioms occurrences
end NMB_OwnedResult
