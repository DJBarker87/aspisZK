import NMS_R2Tail242
import NMS_R2N_ScanRegular
import NMS_R2N_ScanScalar
import NMS_R2Facts242
set_option autoImplicit false
noncomputable section
namespace NMS_R2PoolSites
open Aeneas Aeneas.Std AdapterRw
open NMS_R2Tail242 NMS_R2N_Interpreted
/-- Representation image of the fixed CLOSED scanner source with its actual
Box site. The existential is solely a carrier conversion, never an
independently chosen successful execution or arbitrary child operation. -/
def scan (L : RSL.PoolLib) (candidate : Candidate → L.Afterstate) (data : RSL.Bytes) :
 RSL.RS (L.Afterstate × Nat) := fun env observation =>
 ∃ rawData rawObservation, NMS_R2N_RSLScalars.bytes rawData = data ∧
  NMS_R2N_ScanSites.interpreted rawData env rawObservation ∧
  observation = mapObs (NMS_R2N_RSLError.reply (scanValue L candidate)) rawObservation

/-- Full representation image, including rejected reconstruction and both
private Box-site aborts before a later validation error. -/
def reconstruct (L : RSL.PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement)
 (q : L.Request) (auth : RSL.Authenticated) (c : L.Afterstate) : RSL.RS L.Statement :=
 fun env observation => ∃ rawQ rawAuth rawC rawObservation,
  request rawQ = q ∧ NMS_R2N_RSLPoolCarriers.authenticated rawAuth = auth ∧ candidate rawC = c ∧
  NMS_R2N_ReconstructSites.meaning rawQ rawAuth rawC env rawObservation ∧
  observation = mapObs (NMS_R2N_RSLError.reply statement) rawObservation

def install (L : RSL.PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement) : RSL.PoolLib :=
 {L with scanProof := scan L candidate,
         reconstruct := reconstruct L request candidate statement}

theorem scan_link (L : RSL.PoolLib) (candidate : Candidate → L.Afterstate) (data : Slice U8) :
 Simulates (NMS_R2N_RSLError.reply (scanValue L candidate))
  (NMS_R2N_ScanSites.interpreted data) (scan L candidate (NMS_R2N_RSLScalars.bytes data)) := by
 intro env observation run
 exact ⟨data,observation,rfl,run,rfl⟩

theorem reconstruct_link (L : RSL.PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement)
 (q : Request) (auth : Auth) (c : Candidate) :
 Simulates (NMS_R2N_RSLError.reply statement)
  (NMS_R2N_ReconstructSites.meaning q auth c)
  (reconstruct L request candidate statement (request q)
   (NMS_R2N_RSLPoolCarriers.authenticated auth) (candidate c)) := by
 intro env observation run
 exact ⟨q,auth,c,observation,rfl,rfl,rfl,run,rfl⟩

/-- Scanner width is derived from the CLOSED source at the same run. No
parent proof extent, child success, or allocator success premise is added. -/
theorem scanner_extent (L : RSL.PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement) :
 NMS_R2Facts242.ScannerExtent (install L request candidate statement) := by
 intro data env scanned events run
 obtain ⟨rawData,rawObservation,_,source,same⟩ := run
 cases rawObservation with
 | mk exit before =>
   cases exit with
   | abort => cases same
   | diverge => cases same
   | ret reply =>
     cases reply with
     | Err error => cases same
     | Ok rawScanned =>
       have mapped : scanned = scanValue L candidate rawScanned := by
         exact Except.ok.inj (RSL.Exit.ret.inj (congrArg RSL.Obs.exit same))
       rw [mapped]
       exact NMS_R2N_ScanScalar.proof_value rawData rawScanned
         (NMS_R2N_ScanRegular.source_return rawData env _ before source)
#print axioms scan_link
#print axioms reconstruct_link
#print axioms scanner_extent
end NMS_R2PoolSites
