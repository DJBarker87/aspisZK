import NMT_345Checkpoint
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
structure CheckpointData (W : Type) extends Selected W where
 checkpointData : Slice U8

def dataCall (a : Account) : Result (core.result.Result (Slice U8) PE) :=
 NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (fun e => .ok e) a
/-- Direct SAME-input transport to the canonical emitted getter. The Err
payload is cloned by std identity; no variant or String is discarded. -/
theorem data_transport (a : Account) : dataCall a =
 mapOuter (mapCore id fromPE)
  (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
   (NGL_CloneDomain.install baseOps) (toAccount a)) := by
 rw [NGL_CloneDomain.data_result]
 unfold dataCall NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data toAccount
 cases a.bytes <;> simp [mapCore,mapOuter,from_toPE]
/-- CLOSED getter packet on its exact snapshot-error domain. -/
theorem data_closed (a : Account)
 (domain : ∀ e, (toAccount a).bytes = .Err e → NGL_CloneDomain.SnapshotError e) :
 dataCall a = .ok (mapCore id fromPE
  (NHJ_DataPacket.G (toAccount a) (NHJ_DataPacket.childReply (toAccount a)))) := by
 rw [data_transport, NHJ_DataPacket.substitute _ _ domain]
 rfl
/-- Generic emitted/std law complements that restricted native packet. -/
theorem data_std (a : Account) : dataCall a =
 .ok (match a.bytes with | .Ok v => .Ok v.deref | .Err e => .Err e) := by
 unfold dataCall NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data
 cases a.bytes <;> rfl

def checkpointDataStep {W : Type} (s : Selected W)
 (next : CheckpointData W → Result Ret) : Result Ret :=
 tryStep (dataCall s.checkpointAccount) (fun bytes => next ⟨s,bytes⟩)
theorem checkpointData_std {W : Type} (s : Selected W)
 (next : CheckpointData W → Result Ret) :
 checkpointDataStep s next =
 match s.checkpointAccount.bytes with
 | .Ok v => next ⟨s,v.deref⟩
 | .Err e => .ok (.Err e) := by
 unfold checkpointDataStep
 rw [data_std]
 cases s.checkpointAccount.bytes <;> rfl
#print axioms data_transport
#print axioms data_closed
#print axioms data_std
#print axioms checkpointData_std
end NMT_345
