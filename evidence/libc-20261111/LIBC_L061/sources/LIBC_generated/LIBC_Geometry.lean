import LIBC_ResultGraph
import LIBC_Usize
import LIB_VCarriers
import NFN_GeometryPart08
import NFW_PreparedPort
set_option autoImplicit false
noncomputable section
namespace LIBC_Geometry
open Aeneas Aeneas.Std Result AspisR1 RSL
abbrev Args := LIB_VCarriers.Prepared × Nat × Nat
def Domain (a : Args) : Prop :=
 (LIBC_Usize.raw a.2.1).val=a.2.1 ∧ (LIBC_Usize.raw a.2.2).val=a.2.2 ∧
 NFN_NFB_RangeTrace.Deployed (LIBC_Usize.raw a.2.1) (LIBC_Usize.raw a.2.2) ∧
 (∀ q∈a.1.queries.val,q.val<262144) ∧ a.1.queries.val.Nodup
def port : core.result.Result LIB_VCarriers.Geo VTop_Stages.verifier.Error →
 Except LIB_VCarriers.VErr LIB_VCarriers.Geo
 | .Ok g => .ok g | .Err e => .error e
def model (a : Args) (_ : Env) :=
 Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted a.1.queries
  (LIBC_Usize.raw a.2.1) (LIBC_Usize.raw a.2.2)
/-- On either frozen positive deployed range the first Vec capacity is reached
before any digest/observable effect. All later fresh allocations have the SAME
empty prefix; no post-abort heap or value is part of the law. -/
def law (a : Args) : Spec (Except LIB_VCarriers.VErr LIB_VCarriers.Geo) := fun env o =>
 o = LIB_Carriers.resultObs port [] (model a env) ∨ (Domain a ∧ o=⟨.abort,[]⟩)
def child : Child Args (Except LIB_VCarriers.VErr LIB_VCarriers.Geo) := ⟨Domain,law⟩
def value (a : Args) (env : Env) := LIBC_ResultGraph.value port (.error .Query) (model a env)
theorem returns (a : Args) (env : Env) : NND_Returned.Returns (child.law a) env (value a env) := by
 intro o r h hr
 rcases h with hg | ⟨_,ha⟩
 · exact LIBC_ResultGraph.returns port (.error .Query) (model a) (fun _ => []) env o r hg hr
 · subst o
   cases hr
/-- Complete frozen emitted-copy Result, including rejected/stopped arms,
with the fixed CLOSED arithmetic/geometry dictionary and SAME query array. -/
theorem source (a : Args) (env : Env) :
 Port3_QueryInstall.result
  (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.resultMap NFN_NEW_GeometryRawInterface.answer
   (NEW_GeometryActual.verifier.QueryGeometry.for_range a.1.queries
    (LIBC_Usize.raw a.2.1) (LIBC_Usize.raw a.2.2))) = model a env :=
 NFN_NEW_GeometryComplete.complete _ _ _
theorem graph (a : Args) (env : Env) (o : Obs (Except LIB_VCarriers.VErr LIB_VCarriers.Geo)) :
 child.law a env o ↔ o = LIB_Carriers.resultObs port [] (model a env) ∨ (Domain a ∧ o=⟨.abort,[]⟩) := Iff.rfl
theorem same_queries (a : Args) :
 (AspisR1.NFW_PreparedPort.prepared a.1).queries = a.1.queries := rfl
#print axioms returns
#print axioms source
#print axioms graph
#print axioms same_queries
end LIBC_Geometry
