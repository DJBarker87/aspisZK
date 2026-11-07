import LIBB_PoolScan
import LIBB_ObservationMap
set_option autoImplicit false
noncomputable section
namespace LIBB_ScannerExtent
open Aeneas Aeneas.Std RSL
/-- Export the caller's proof-width clause from the SAME scanned value. -/
theorem extent (data : Bytes) (env : Env) (scanned : LIBB_PoolCarriers.Afterstate × Nat)
 (events : List Event) (run : LIBB_PoolScan.scanProof data env ⟨.ret (.ok scanned),events⟩) :
 scanned.2 = PROOF_BYTES := by
 unfold LIBB_PoolScan.scanProof at run
 split at run
 · obtain ⟨r,source,same⟩ := LIBB_ObservationMap.return_source _ _ _ _ _ run
   cases r with
   | Err e => cases same
   | Ok s =>
     have hs : scanned = (s.candidate_afterstate,s.proof_length.val) := Except.ok.inj same
     rw [hs]
     exact NMS_R2N_ScanScalar.proof_value _ s
       (NMS_R2N_ScanRegular.source_return _ env _ events source)
 · cases congrArg Obs.exit run
#print axioms extent
end LIBB_ScannerExtent
end
