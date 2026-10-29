import R1Z.PV_RunJoin_ActualData59
import R1Z.PV_RunJoin_ActualPlanSources59
/-! Fixed symbolic families for NativeCallback55.runOf. The source slice
returns proof bytes only; it does not return account paths or afterstate
bytes. Those three unused PublicationInput fields are empty here, and no
full observer/account-data association is claimed by these definitions. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualRun
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

def data : Phase → PV_RunJoin_OpeningImages54.Data := PV_RunJoin_ActualData59.data

def statement (p : Phase) : Bytes :=
  match aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p.public1 with
  | .ok (.Ok out) => bytes out.val
  | _ => []

def plans (p : Phase) : Plan where
  header := PV_RunJoin_ActualPlanSources59.header
  semantic := PV_RunJoin_ActualPlanSources59.publicationBytes p PV_RunJoin_ActualPlanSources59.compactSemantic
  claim := PV_RunJoin_ActualPlanSources59.publicationBytes p PV_RunJoin_ActualPlanSources59.compactClaim
  inactive := PV_RunJoin_ActualPlanSources59.publicationBytes p (fun publication => do
    let encoded ← aspis_core.field.wide_exact.WideExact.to_le_bytes publication.inactive
    alloc.slice.Slice.to_vec core.clone.CloneU8 (← Aeneas.Std.lift (Array.to_slice encoded)))
  root := PV_RunJoin_ActualPlanSources59.publicationBytes p (fun publication => do
    alloc.slice.Slice.to_vec core.clone.CloneU8 (← Aeneas.Std.lift (Array.to_slice publication.root)))
  queries := List.ofFn (PV_RunJoin_ActualPlanSources59.queryPart p)
  slots := List.ofFn (PV_RunJoin_ActualPlanSources59.slot p)
  offOpenings := 10055
  offNodes := 28359
  proofBytes := 57607
  afterstate := []
  statement := statement p
  proofPath := []
  statementPath := []

def runs : Phase → Run := PV_RunJoin_NativeCallback55.runOf data plans

theorem layout (p : Phase) :
    (runs p).plan.queries.length=22 ∧ (runs p).plan.slots.length=6 ∧
    (runs p).plan.offOpenings=10055 ∧ (runs p).plan.offNodes=28359 ∧
    (runs p).plan.proofBytes=57607 := by
  simp only [runs,PV_RunJoin_NativeCallback55.runOf,plans,List.length_ofFn]
  exact ⟨rfl,rfl,rfl⟩

#print axioms data
#print axioms statement
#print axioms plans
#print axioms runs
#print axioms layout
end R1Z.PV_RunJoin_ActualRun
