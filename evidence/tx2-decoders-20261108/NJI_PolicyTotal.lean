import NJI_PolicyCut
import NJI_LengthCuts
set_option autoImplicit false
noncomputable section
namespace NJI_PolicyTotal
open Aeneas Aeneas.Std Result NJI_PolicyPort

/-- Two disjoint native stages: scalar first guard for every length, then the
104-byte source cut. This is not an acceptance precondition. -/
def Cut (b : Slice U8) (log : Option P) (out : core.result.Result P F) : Prop :=
 if len : b.val.length=104 then
   NJI_PolicyCut.Cut b (NJI_PolicyCut.closedReply b len) log out
 else log=none ∧ out=.Err .WrongLength

theorem native_source (b : Slice U8) (log : Option P) (out : core.result.Result P F)
 (h : Cut b log out) : ok out=NJI_PolicyParser.raw b := by
 unfold Cut at h
 split at h
 · rename_i len
   exact NJI_PolicyCut.native_source b len log out h
 · rename_i wrong
   rw [NJI_PolicyParser.source]
   simp only [NJI_PolicyParser.body,dif_neg wrong]
   exact congrArg Result.ok h.2

#print native_source
#print axioms native_source
end NJI_PolicyTotal
