import NMX_R6_ScanComplete
import LIBB_PoolReconstruct
set_option autoImplicit false
noncomputable section
namespace NMX_R6_Children
open Aeneas Aeneas.Std Result NMX_R6_Observation
open NMS_R2N_Interpreted

def scan (data : RSL.Bytes) : RSL.Obs (Except RSL.ProgramError (LIBB_PoolCarriers.Afterstate × Nat)) :=
 if bound : data.length ≤ Usize.max then
  mapObs LIBB_PoolScan.reply (scalar (AspisR1.NFY_JHf_Scan.source (LIBB_Bytes.fromBytes data bound)))
 else ⟨.abort,[]⟩

theorem scan_member (data : RSL.Bytes) (env : RSL.Env) :
 LIBB_PoolScan.scanProof data env (scan data) := by
 unfold LIBB_PoolScan.scanProof scan
 split
 · apply LIBB_ModelGraph.mapped_member
   have h := NMX_R6_ScanComplete.complete (LIBB_Bytes.fromBytes data ‹_›) env
   rw [NMS_R2N_ScanSites.erases] at h
   exact h
 · rfl

theorem reconstruct_complete (q : LIBB_PoolCarriers.Request) (a : LIBB_AuthCarrier.Raw)
 (c : LIBB_PoolCarriers.Afterstate) :
 Complete (NMS_R2N_ReconstructSites.meaning q a c) (AspisR1.NFY_JHf_ReconstructionSlot.source q a c) := by
 unfold NMS_R2N_ReconstructSites.meaning
 split
 · have h := complete_bind RSL.Spec.alloc (ok ()) _ (fun _ =>
     AspisR1.NFY_JHf_ReconstructionSlot.source q a c) allocate (fun _ => lift _)
   exact complete_bind RSL.Spec.alloc (ok ()) _ (fun _ =>
     AspisR1.NFY_JHf_ReconstructionSlot.source q a c) allocate (fun _ => h)
 · exact lift _

def reconstruct (q : LIBB_PoolCarriers.Request) (a : RSL.Authenticated)
 (c : LIBB_PoolCarriers.Afterstate) : RSL.Obs (Except RSL.ProgramError LIBB_PoolCarriers.Statement) :=
 match LIBB_AuthCarrier.raw a with
 | none => ⟨.abort,[]⟩
 | some raw => mapObs LIBB_PoolReconstruct.reply
  (scalar (AspisR1.NFY_JHf_ReconstructionSlot.source q raw c))

theorem reconstruct_member (q : LIBB_PoolCarriers.Request) (a : RSL.Authenticated)
 (c : LIBB_PoolCarriers.Afterstate) (env : RSL.Env) :
 LIBB_PoolReconstruct.reconstruct q a c env (reconstruct q a c) := by
 unfold LIBB_PoolReconstruct.reconstruct reconstruct
 cases h : LIBB_AuthCarrier.raw a with
 | none => rfl
 | some raw =>
   exact LIBB_ModelGraph.mapped_member _ _ env _ (reconstruct_complete q raw c env)

#print axioms scan_member
#print axioms reconstruct_complete
#print axioms reconstruct_member
end NMX_R6_Children
end
