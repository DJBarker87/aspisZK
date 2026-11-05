import NHJ_SnapshotReference.Funs
import NHJ_StdCopy
import NGL_MetaReferenceModel
import NGL_SnapshotModel
set_option autoImplicit false
noncomputable section
namespace NHJ_SnapshotAssociation
open Aeneas Aeneas.Std Result
abbrev PE := NGL_MetaReference.ProgramError
abbrev Key := NGL_ReadonlyModel.Key
abbrev Bytes := Slice U8
abbrev RAccount := NHJ_SnapshotReference.OwnedAccount
abbrev Account := NGL_SnapshotModel.Account

def port (a : RAccount) : Account :=
  ⟨a.key,a.owner,a.is_signer,a.is_writable,a.executable,
    NGL_MetaReferenceModel.port a.length,NGL_MetaReferenceModel.port a.bytes⟩

abbrev copy := NHJ_StdCopy.copy

/-- The SDK trust row supplies the sole reachable borrowed error constructor.
No conclusion about String.clone is required or asserted. -/
def BorrowDomain (borrowed : core.result.Result Bytes PE) : Prop :=
  ∀ e, borrowed = .Err e → e = NGL_MetaReference.ProgramError.AccountBorrowFailed

theorem source (key owner : Key) (s w e : Bool) (l1 l2 : Usize)
    (borrowed : core.result.Result Bytes PE) (domain : BorrowDomain borrowed) :
    (do let a ← NHJ_SnapshotReference.snapshot_ref key owner s w e l1 l2 borrowed
        ok (port a)) =
      NGL_SnapshotModel.run copy key owner s w e l1 l2
        (NGL_MetaReferenceModel.port borrowed) := by
  cases borrowed with
  | Err error =>
    have same := domain error rfl
    subst error
    rfl
  | Ok bytes =>
    by_cases h1 : Slice.len bytes = l1
    · simp [NHJ_SnapshotReference.snapshot_ref,NGL_SnapshotModel.run,
        copy,NHJ_StdCopy.copy,NHJ_StdCopy.to_vec_exact,h1,port,NGL_MetaReferenceModel.port,NGL_ErrorCarrier.from_meta]
    · by_cases h2 : Slice.len bytes = l2
      · simp [NHJ_SnapshotReference.snapshot_ref,NGL_SnapshotModel.run,
          copy,NHJ_StdCopy.copy,NHJ_StdCopy.to_vec_exact,h1,h2,port,NGL_MetaReferenceModel.port,NGL_ErrorCarrier.from_meta]
      · simp [NHJ_SnapshotReference.snapshot_ref,NGL_SnapshotModel.run,
          copy,NHJ_StdCopy.copy,NHJ_StdCopy.to_vec_exact,h1,h2,port,NGL_MetaReferenceModel.port,NGL_ErrorCarrier.from_meta]
#print axioms source
end NHJ_SnapshotAssociation
