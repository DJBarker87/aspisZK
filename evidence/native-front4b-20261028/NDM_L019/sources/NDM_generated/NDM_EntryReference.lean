import S2W_D189Entry
import NDM_SnapshotRef.Funs
set_option autoImplicit false
namespace NDM_EntryReference
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.S2W_D189Entry
abbrev Metadata := solana_pubkey.Pubkey × solana_pubkey.Pubkey × Bool × Bool × Bool

def materialize (metadata : Metadata) (length : Usize) (bytes : Option (Slice U8)) :
 r1_pool_adapter.owned.OwnedAccount :=
 let (key,owner,signer,writable,executable) := metadata
 {key:=key,owner:=owner,is_signer:=signer,is_writable:=writable,executable:=executable,
 length:=.Ok length,bytes:=match bytes with | some b=>.Ok b | none=>.Err .InvalidAccountData}

def reference (e : Entry) (a : Nat) (limit1 limit2 : Usize) : Result
 r1_pool_adapter.owned.OwnedAccount := do
 let bytes := e.buffers (e.handles a).1
 let record := (e.records (e.handles a).1).owned
 let admitted ← NDM_SnapshotRef.snapshot_select_ref (Slice.len bytes) limit1 limit2
 let (metadata,length,out) ← NDM_SnapshotRef.snapshot_value_ref
  (record.key,record.owner,record.is_signer,record.is_writable,record.executable)
  (Slice.len bytes) admitted bytes
 ok (materialize metadata length out)

/-- Exact computed cohort snapshot on representable length limits. Native allocation/SDK
 interpretation remains separate; this theorem adds no output-shaped premise. -/
theorem value (e : Entry) (a : Nat) (limit1 limit2 : Usize) :
 reference e a limit1 limit2 = ok (e.snapshot a limit1.val limit2.val) := by
 let bytes := e.buffers (e.handles a).1
 have size1 : Slice.len bytes=limit1 ↔ bytes.val.length=limit1.val := by
  constructor <;> intro h <;> scalar_tac
 have size2 : Slice.len bytes=limit2 ↔ bytes.val.length=limit2.val := by
  constructor <;> intro h <;> scalar_tac
 by_cases first : Slice.len bytes=limit1
 · have size := size1.mp first
   simp [reference,NDM_SnapshotRef.snapshot_select_ref,NDM_SnapshotRef.snapshot_value_ref,
    materialize,Entry.snapshot,bytes] at first size ⊢
   simp [first,size]
 · by_cases second : Slice.len bytes=limit2
   · have size := size2.mp second
     simp [reference,NDM_SnapshotRef.snapshot_select_ref,NDM_SnapshotRef.snapshot_value_ref,
      materialize,Entry.snapshot,bytes] at first second size ⊢
     simp [first,second,size]
   · have n1 := mt size1.mpr first
     have n2 := mt size2.mpr second
     simp [reference,NDM_SnapshotRef.snapshot_select_ref,NDM_SnapshotRef.snapshot_value_ref,
      materialize,Entry.snapshot,bytes] at first second n1 n2 ⊢
     simp [first,second,n1,n2]

#print axioms value
end NDM_EntryReference
