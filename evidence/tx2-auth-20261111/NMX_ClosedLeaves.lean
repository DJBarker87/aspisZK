import NMX_SourceModel
import NFU_AdapterGetters
import NHJ_DataPacket
import NHJ_LengthPacket
import NHJ_DistinctPacket
import NIM_NHJ_ReadonlyPacket
import NHJ_CheckpointPacket
set_option autoImplicit false
noncomputable section
namespace NMX_ClosedLeaves
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- Instantiate CLOSED key owner at the exact entered account, retaining its
full source event. This is a SOURCE-handler step, not a native packet. -/
theorem key {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (before : W) :
 source ops owners (.key a) before =
 End.returned (.Ok a.key) before [.key a (.ok a.key)] := by
 simp only [source, NFU_AdapterGetters.key, rawResult,returned]
/-- Canonical data packet applied at SAME bytes/error argument. SnapshotError
is left visible on this source step; it must be a233 own-input caller clause. -/
theorem data {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (before : W)
 (errors : ∀ e, a.bytes = .Err e → NGL_CloneDomain.SnapshotError e) :
 source (NGL_CloneDomain.install ops) owners (.data a) before =
 End.returned (NHJ_DataPacket.G a (NHJ_DataPacket.childReply a)) before
 [.data a (.ok (NHJ_DataPacket.G a (NHJ_DataPacket.childReply a)))] := by
 simp only [source,NHJ_DataPacket.substitute ops a errors,returned]

theorem readonly {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (expected : solana_pubkey.Pubkey)
 (before : W) :
 source (NGL_ReadonlyModel.install ops) owners (.readonlyAccount a expected) before =
 let reply := NHJ_ReadonlyPacket.G (NHJ_ReadonlyPacket.arguments a expected)
   (NHJ_ReadonlyPacket.accepted a.owner expected a.is_signer a.is_writable a.executable)
 End.returned reply before [.readonlyAccount a expected (.ok reply)] := by
 simp only [source,NHJ_ReadonlyPacket.readonly ops a expected,returned]

theorem distinct {W : Type} (ops : Ops) (owners : Owners)
 (accounts : Array r1_pool_adapter.owned.OwnedAccount 7#usize) (before : W) :
 source (NGL_ReadonlyModel.install ops) owners (.distinct accounts) before =
 returned before [.distinct accounts (NGL_DistinctInduction.reference accounts)]
 (NGL_DistinctInduction.reference accounts) := by
 simp only [source,NHJ_DistinctPacket.seven ops accounts]

theorem checkpoint {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey)
 (writable : Bool) (before : W) (domain : NGL_LengthCarrier.domain a.length) :
 source (NGL_CheckpointModel.install ops) owners (.checkpointGuard a program writable) before =
 let reply := NHJ_CheckpointPacket.G a program writable (NHJ_CheckpointPacket.encode a.length)
 End.returned reply before [.checkpointGuard a program writable (.ok reply)] := by
 simp only [source,NHJ_CheckpointPacket.substitute ops a program writable domain,returned]
#print axioms key
#print axioms data
#print axioms readonly
#print axioms distinct
#print axioms checkpoint
end NMX_ClosedLeaves
end
