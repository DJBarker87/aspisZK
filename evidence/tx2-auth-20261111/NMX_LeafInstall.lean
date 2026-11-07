import NMX_ClosedLeaves
set_option autoImplicit false
noncomputable section
namespace NMX_LeafInstall
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- One unchanged installation for all readonly/data/length occurrences.
This local child installation is not asserted equal to a deployed dictionary. -/
abbrev install := NGL_CheckpointModel.install

theorem readonly {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (expected : solana_pubkey.Pubkey) (before : W) :
 source (install ops) owners (.readonlyAccount a expected) before =
 let reply := NHJ_ReadonlyPacket.G (NHJ_ReadonlyPacket.arguments a expected)
   (NHJ_ReadonlyPacket.accepted a.owner expected a.is_signer a.is_writable a.executable)
 End.returned reply before [.readonlyAccount a expected (.ok reply)] := by
 change source (NGL_ReadonlyModel.install (install ops)) owners (.readonlyAccount a expected) before = _
 exact NMX_ClosedLeaves.readonly (install ops) owners a expected before

theorem data {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (before : W)
 (errors : ∀ e, a.bytes = .Err e → NGL_CloneDomain.SnapshotError e) :
 source (install ops) owners (.data a) before =
 End.returned (NHJ_DataPacket.G a (NHJ_DataPacket.childReply a)) before
 [.data a (.ok (NHJ_DataPacket.G a (NHJ_DataPacket.childReply a)))] := by
 change source (NGL_CloneDomain.install (install ops)) owners (.data a) before = _
 exact NMX_ClosedLeaves.data (install ops) owners a before errors

theorem distinct {W : Type} (ops : Ops) (owners : Owners)
 (accounts : Array r1_pool_adapter.owned.OwnedAccount 7#usize) (before : W) :
 source (install ops) owners (.distinct accounts) before =
 returned before [.distinct accounts (NGL_DistinctInduction.reference accounts)]
 (NGL_DistinctInduction.reference accounts) := by
 change source (NGL_ReadonlyModel.install (install ops)) owners (.distinct accounts) before = _
 exact NMX_ClosedLeaves.distinct (install ops) owners accounts before

theorem checkpoint {W : Type} (ops : Ops) (owners : Owners)
 (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey)
 (before : W) (domain : NGL_LengthCarrier.domain a.length) :
 source (install ops) owners (.checkpointGuard a program false) before =
 let reply := NHJ_CheckpointPacket.G a program false (NHJ_CheckpointPacket.encode a.length)
 End.returned reply before [.checkpointGuard a program false (.ok reply)] :=
 NMX_ClosedLeaves.checkpoint ops owners a program false before domain
#print axioms readonly
#print axioms data
#print axioms distinct
#print axioms checkpoint
end NMX_LeafInstall
end
