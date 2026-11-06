import NLM_ActualRead
import NLE_SnapshotClause
set_option autoImplicit false
noncomputable section
namespace NLM_CheckedExtent
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry
/-- The successful getter and the actual length comparison determine the end;
no independent 58295-byte account or chosen child range is a root premise. -/
theorem end_value (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8) (end_ : Usize)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot 0 58295 58295)=.ok (.Ok bytes))
 (guard : Slice.len bytes=end_) : end_.val=58295 := by
 have extent := NLE_SnapshotClause.proof_bytes e bytes
  (NLM_ActualRead.snapshot_bytes ops e 0 58295 58295 bytes read)
 have same := congrArg (fun n : Usize => n.val) guard
 rw [Slice.len_val] at same
 omega

theorem proof_length (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8)
 (end_ length : Usize)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot 0 58295 58295)=.ok (.Ok bytes))
 (guard : Slice.len bytes=end_) (checked : end_.val=688+length.val) : length.val=57607 := by
 have extent := end_value ops e bytes end_ read guard
 omega
#print end_value
#print proof_length
#print axioms end_value
#print axioms proof_length
end NLM_CheckedExtent
