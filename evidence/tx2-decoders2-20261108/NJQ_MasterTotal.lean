import NJQ_MasterCut
set_option autoImplicit false
noncomputable section
namespace NJQ_MasterTotal
open Aeneas Aeneas.Std Result NJQ_Master
attribute [local instance] Classical.propDecidable

def Cut (b : Slice U8) (out : core.result.Result M F) : Prop :=
 if len : b.val.length=384 then NJQ_MasterCut.Cut b len out else out=.Err .WrongLength

theorem native_source (b : Slice U8) (out : core.result.Result M F) (h : Cut b out) :
 ok out=reference b := by
 unfold Cut at h
 split at h
 · rename_i len
   exact NJQ_MasterCut.native_source b len out h
 · rename_i wrong
   rw [source]
   simp only [model,dif_neg wrong]
   exact congrArg Result.ok h

set_option pp.proofs false in
#print native_source
#print axioms native_source
end NJQ_MasterTotal
