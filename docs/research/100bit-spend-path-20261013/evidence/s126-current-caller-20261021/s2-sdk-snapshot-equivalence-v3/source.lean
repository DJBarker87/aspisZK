import S2SdkSnapshotReferenceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.SnapshotReference

/-- Full definitional transparency for two symbolic source bodies only.
This generates Eq.refl; the kernel checks the resulting proof independently. -/
elab "snapshot_defeq" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  unless target.isAppOfArity ``Eq 3 do throwError "Expected source equality"
  let args := target.getAppArgs
  unless ← withTransparency .all <| isDefEq args[1]! args[2]! do
    throwError "Source bodies are not definitionally equal"
  goal.assign (← mkEqRefl args[1]!)
  replaceMainGoal []

theorem public_snapshot_eq (bytes : alloc.vec.Vec U8) :
    public_snapshot bytes=alloc.vec.CloneVec.clone core.clone.CloneU8 bytes := rfl

theorem proof_snapshot_eq (bytes : alloc.vec.Vec U8) :
    proof_snapshot bytes=alloc.vec.CloneVec.clone core.clone.CloneU8 bytes := rfl

/-- Exact full-parent equality of the pure snapshot fission. No SDK field,
error/status, ordinary failure/divergence or child result is abstracted. -/
theorem body_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : Slice U8) (guards : LiveGuards) :
    SnapshotReference.owned_stage1_body ops program sdk data guards =
      SdkReference.owned_stage1_body ops program sdk data guards := by
  unfold SnapshotReference.owned_stage1_body SdkReference.owned_stage1_body
  simp only [public_snapshot_eq,proof_snapshot_eq]
  snapshot_defeq

theorem stage1_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) :
    SnapshotReference.owned_stage1 ops program sdk data =
      SdkReference.owned_stage1 ops program sdk data := by
  unfold SnapshotReference.owned_stage1 SdkReference.owned_stage1
  rw [body_eq]
  snapshot_defeq

#print axioms public_snapshot_eq
#print axioms proof_snapshot_eq
#print axioms body_eq
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.SnapshotReference
