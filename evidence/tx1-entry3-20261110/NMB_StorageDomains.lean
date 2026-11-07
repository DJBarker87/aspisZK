import NMB_SnapshotPacket
set_option autoImplicit false
noncomputable section
namespace NMB_StorageDomains
open Aeneas Aeneas.Std Result AspisR1
/-- The CLOSED owned-accessor domains hold on EVERY computed snapshot,
including deferred malformed-length errors, before any child acceptance. -/
theorem proof (x : NMB_Input.Input) :
 NGL_StorageCases.Domain (x.snapshot 0 58295 58295) :=
 (NHJ_SnapshotPacket.caller_domains (NMB_SnapshotPacket.entryAt x 0)).1 0
theorem public_input (x : NMB_Input.Input) :
 NGL_StorageCases.Domain (x.snapshot 1 1880 1880) :=
 (NHJ_SnapshotPacket.caller_domains (NMB_SnapshotPacket.entryAt x 1)).1 1
theorem checkpoint (x : NMB_Input.Input) :
 NGL_StorageCases.Domain (x.snapshot 2 1768 1768) :=
 (NHJ_SnapshotPacket.caller_domains (NMB_SnapshotPacket.entryAt x 2)).1 2
#print proof
#print public_input
#print checkpoint
#print axioms proof
#print axioms public_input
#print axioms checkpoint
end NMB_StorageDomains
