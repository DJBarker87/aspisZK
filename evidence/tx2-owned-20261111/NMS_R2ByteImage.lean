import NMS_R2PoolSites
set_option autoImplicit false
noncomputable section
namespace NMS_R2ByteImage
open Aeneas Aeneas.Std
open NMS_R2N_RSLScalars
/-- Bit-pattern conversion is injective on every symbolic native slice. -/
theorem injective {a b : Slice U8} (same : bytes a = bytes b) : a = b := by
 apply Subtype.ext
 have inverse := congrArg (fun data => data.map raw8) same
 simp only [bytes,List.map_map,Function.comp_def,u8_left] at inverse
 change a.val.map id = b.val.map id at inverse
 simpa only [List.map_id] using inverse

/-- Logical representation conversion only: no runtime Vec allocation is
introduced by this map. Nonphysical lengths are kept outside the native type. -/
def native (data : RSL.Bytes) (bound : data.length ≤ Usize.max) : Slice U8 :=
 ⟨data.map raw8,by simpa only [List.length_map] using bound⟩

theorem right (data : RSL.Bytes) (bound : data.length ≤ Usize.max) :
 bytes (native data bound) = data := by
 simp only [bytes,native,List.map_map,Function.comp_def,u8_right]
 change data.map id = data
 exact List.map_id data

theorem left (a : Slice U8) (bound : (bytes a).length ≤ Usize.max) :
 native (bytes a) bound = a := injective ((right _ _).trans rfl)

/-- The fixed scanner law has exactly the original native input image;
its existential carrier representation adds no alternate byte buffer. -/
theorem scan_exact (L : RSL.PoolLib)
 (candidate : NMS_R2Tail242.Candidate → L.Afterstate) (data : Slice U8)
 (env : RSL.Env) (o : RSL.Obs (Except RSL.ProgramError (L.Afterstate × Nat))) :
 NMS_R2PoolSites.scan L candidate (bytes data) env o ↔
 ∃ rawObservation, NMS_R2N_ScanSites.interpreted data env rawObservation ∧
  o = NMS_R2N_Interpreted.mapObs (NMS_R2N_RSLError.reply (NMS_R2Tail242.scanValue L candidate)) rawObservation := by
 constructor
 · rintro ⟨rawData,rawObservation,same,run,mapped⟩
   have original : rawData = data := injective same
   subst rawData
   exact ⟨rawObservation,run,mapped⟩
 · rintro ⟨rawObservation,run,mapped⟩
   exact ⟨data,rawObservation,rfl,run,mapped⟩
#print axioms injective
#print axioms right
#print axioms left
#print axioms scan_exact
end NMS_R2ByteImage
