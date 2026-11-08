import NMX_R7_Verify241
import NMS_R2ErrorSource
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Error241
open Aeneas Aeneas.Std Result AdapterRw
abbrev V := LIBB_V2Star.library
abbrev Raw := aspis_r1_cost_probe.verifier.Error

def embed : Raw → V.VErr
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def raw : V.VErr → Raw
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

theorem left (e : Raw) : raw (embed e) = e := by cases e <;> rfl
theorem right (e : V.VErr) : embed (raw e) = e := by cases e <;> rfl

theorem format (e : Raw) :
 NIJ_ErrorJoin.formatted (LIB_ErrorDebug.adapter (embed e)) = "r1:error:" ++ V.debug (embed e) :=
 LIB_ErrorDebug.native_format _

theorem full (r : core.result.Result Unit Raw) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply id)
  (NMS_Effect241.mapError r (NMS_R2ErrorSource.callback V embed))
  (RSL.TX2_241.mapVErr V (NMS_R2ErrorSource.verifierReply V embed r)) :=
 NMS_R2ErrorSource.full V embed r
#print axioms left
#print axioms right
#print axioms format
#print axioms full
end NMX_R7_Error241
end
