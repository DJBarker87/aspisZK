import NLM_CheckedAddFacts
set_option autoImplicit false
noncomputable section
namespace NLW_GetterSuccess
open Aeneas Aeneas.Std Result AdapterRw
abbrev Owned := r1_pool_adapter.owned.OwnedAccount
/-- Successful returned bytes identify the stored buffer for ACTUAL Ops.
An arbitrary error-clone slot cannot turn a stored Err into Ok bytes. -/
theorem stored (ops : Ops) (a : Owned) (bytes : Slice U8)
 (read : r1_pool_adapter.owned.OwnedAccount.data ops a=.ok (.Ok bytes)) :
 a.bytes=.Ok bytes := by
 unfold r1_pool_adapter.owned.OwnedAccount.data at read
 cases hb : a.bytes with
 | Ok value =>
   simp only [hb] at read
   cases read
   rfl
 | Err err =>
   simp only [hb] at read
   cases he : ops.op35 err <;> simp [he,Bind.bind] at read
/-- Direct successful getter evaluation, independent of error cloning. -/
theorem returned (ops : Ops) (a : Owned) (bytes : Slice U8)
 (stored : a.bytes=.Ok bytes) :
 r1_pool_adapter.owned.OwnedAccount.data ops a=.ok (.Ok bytes) := by
 simp only [r1_pool_adapter.owned.OwnedAccount.data,stored]
 rfl
#print stored
#print returned
#print axioms stored
#print axioms returned
end NLW_GetterSuccess
