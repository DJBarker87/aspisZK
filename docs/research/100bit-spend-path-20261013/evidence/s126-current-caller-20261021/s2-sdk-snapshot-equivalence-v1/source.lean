import S2SdkSnapshotReferenceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.SnapshotReference

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
  rfl

theorem stage1_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) :
    SnapshotReference.owned_stage1 ops program sdk data =
      SdkReference.owned_stage1 ops program sdk data := by
  rfl

#print axioms public_snapshot_eq
#print axioms proof_snapshot_eq
#print axioms body_eq
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.SnapshotReference
