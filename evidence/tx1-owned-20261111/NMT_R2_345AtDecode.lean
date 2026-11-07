import NMT_345BoundaryDecode
import NMT_R2_DecoderInstall
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtDecode
open Aeneas Aeneas.Std NMT_345 RSL

def install (internal outer : Bool) (c : Calls) : Calls :=
 {c with c12 := NMT_R2_DecoderInstall.native internal outer}

theorem boundary {W : Type} (internal outer : Bool) (c : Calls) (s : PublicData W) :
 raw06 (install internal outer c) s =
 tryStep (NMT_R2_DecoderInstall.native internal outer s.publicData)
  (fun st => raw07 (install internal outer c) ⟨s,st⟩) := boundaryDecode _ s

theorem observation {W : Type} (internal outer : Bool) (s : PublicData W) (env : Env) :
 NMT_R2_DecoderObservation.reference (s.publicData.val.map byte) env
  (NMT_R2_EmittedData.observe id (NMT_R2_DecoderInstall.native internal outer s.publicData)) :=
 NMT_R2_DecoderInstall.law internal outer s.publicData env
#print axioms boundary
#print axioms observation
end NMT_R2_345AtDecode
end
