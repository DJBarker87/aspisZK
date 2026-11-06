import NJQ_RegistryCut
set_option autoImplicit false
noncomputable section
namespace NJQ_RegistryTotal
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable

def Cut (b : Slice U8) (log : Option R) (out : core.result.Result R F) : Prop :=
 if len : b.val.length=128 then
  NJQ_RegistryCut.Cut b len (NJQ_RegistryCut.closedReply b len) log out
 else log=none ∧ out=.Err .WrongLength

theorem native_source (b : Slice U8) (log : Option R) (out : core.result.Result R F)
 (h : Cut b log out) : ok out=NJQ_Registry.reference b := by
 unfold Cut at h
 split at h
 · rename_i len
   exact NJQ_RegistryCut.native_source b len log out h
 · rename_i wrong
   rw [NJQ_Registry.source]
   simp only [NJQ_Registry.model,dif_neg wrong]
   exact congrArg Result.ok h.2

#print native_source
#print axioms native_source
end NJQ_RegistryTotal
