import NJQ_EntryCut
set_option autoImplicit false
noncomputable section
namespace NJQ_EntryTotal
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable

def Cut (b : Slice U8) (log : Option E) (out : core.result.Result E F) : Prop :=
 if len : b.val.length=192 then
  NJQ_EntryCut.Cut b len (NJQ_EntryCut.closedReply b len) log out
 else log=none ∧ out=.Err .WrongLength

theorem native_source (b : Slice U8) (log : Option E) (out : core.result.Result E F)
 (h : Cut b log out) : ok out=NJQ_Entry.reference b := by
 unfold Cut at h
 split at h
 · rename_i len
   exact NJQ_EntryCut.native_source b len log out h
 · rename_i wrong
   rw [NJQ_Entry.source]
   simp only [NJQ_Entry.model,dif_neg wrong]
   exact congrArg Result.ok h.2

#print native_source
#print axioms native_source
end NJQ_EntryTotal
