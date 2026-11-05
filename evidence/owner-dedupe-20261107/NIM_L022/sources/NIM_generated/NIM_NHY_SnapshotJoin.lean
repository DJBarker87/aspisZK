import NIM_NHY_SnapshotRoot
set_option autoImplicit false
noncomputable section
namespace NHY_SnapshotJoin
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry AspisR1.S2Trust

/-- Explicit Err arm retained by the native logging cut. -/
theorem rejected (key owner : NGL_ReadonlyModel.Key) (s w x : Bool) (l1 l2 : Usize) :
    (do let r ← NHJ_SnapshotReference.snapshot_ref key owner s w x l1 l2
          (.Err NGL_MetaReference.ProgramError.AccountBorrowFailed)
        ok (NHJ_SnapshotAssociation.port r)) =
      ok (⟨key,owner,s,w,x,
        .Err AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed,
        .Err AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed⟩ : NGL_SnapshotModel.Account) := rfl

/-- BOTH arms are interpreted before specializing the runtime entry domain. -/
theorem both_arms (key owner : NGL_ReadonlyModel.Key) (s w x : Bool) (l1 l2 : Usize)
    (b : core.result.Result (Slice U8) NGL_MetaReference.ProgramError)
    (domain : NHJ_SnapshotAssociation.BorrowDomain b) :
    (do let r ← NHJ_SnapshotReference.snapshot_ref key owner s w x l1 l2 b
        ok (NHJ_SnapshotAssociation.port r)) =
      NGL_SnapshotModel.run NHJ_StdCopy.copy key owner s w x l1 l2
        (NGL_MetaReferenceModel.port b) :=
  NHJ_SnapshotAssociation.source key owner s w x l1 l2 b domain

/-- Full root-domain join: SDK success is a conclusion from the computed heap,
not an assumed reply. The original SDK world is restored after guard cleanup.
The root interpretation is relatedness/validity of the SAME entry heap. -/
theorem source {W : Type} (e : Entry) (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L) (w : W) (related : L.related w e.heap)
    (valid : Valid e.heap) (a : Nat) (l1 l2 : Usize) :
    ∃ token owner w1 w2 w3,
      L.run w (.shared a token owner) = (w1,.guard token) ∧
      L.run w1 (.deref token) = (w2,.payload (e.heap.payload (e.heap.accounts a).1)) ∧
      L.run w2 (.drop token) = (w3,.unit) ∧ L.related w3 e.heap ∧
      (let old := (e.records (e.handles a).1).owned
       (do let returned ← NHJ_SnapshotReference.snapshot_ref old.key old.owner
             old.is_signer old.is_writable old.executable l1 l2
             (.Ok (e.buffers (e.handles a).1))
           ok (NHJ_SnapshotAssociation.port returned)) =
         ok (e.snapshot a l1.val l2.val)) := by
  obtain ⟨token,owner,w1,w2,w3,h1,h2,h3,h4⟩ :=
    NHY_SnapshotRoot.returning e L sdk w related valid a
  exact ⟨token,owner,w1,w2,w3,h1,h2,h3,h4,NHJ_SnapshotPacket.cohort_return e a l1 l2⟩

#print axioms rejected
#print axioms both_arms
#print axioms source
end NHY_SnapshotJoin
