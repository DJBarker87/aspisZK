import NLM_Auth064Domain
import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace NLM_Auth064Code
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLM_Auth064
open AspisR1.CheckpointBytes5Effect
abbrev Out (Ambient : Type) := Reply × World Ambient
abbrev ChildCode (Ambient H : Type) := NLM_RowSpec_065.Frame H → World Ambient → Code (Out Ambient)
abbrev ChildObservation (Ambient H : Type) :=
 NLM_RowSpec_065.Frame H → World Ambient → NGP_L181.Observation (Out Ambient)
/-- Hash-effect scheduling of this owned parent. The child Code is the FULL
065 code parameter, not a lift of its outer Result or a chosen hash log.
Physical native cut installation and source-code identification remain open. -/
def code {Ambient H : Type} (common : ChildCode Ambient H) (s : State Ambient H) : Code (Out Ambient) :=
 .step (NLE_ParseInstall.parse s.input.proof) fun result=>
 match result with
 | .Err err => .done (.Err err,s.world)
 | .Ok variant =>
   .step (NHV_ReleaseOps.mark none .Parsed) fun _=>
    common (commonFrame {s with parsed:=some variant}) s.world
/-- A composed MODEL observation. It is never asserted to be the observation
of the frozen Rust without the missing physical/native cuts. -/
def observation {Ambient H : Type} (common : ChildObservation Ambient H)
 (s : State Ambient H) : NGP_L181.Observation (Out Ambient) :=
 match NLE_ParseInstall.parse s.input.proof with
 | .fail err => ⟨.fail err,[]⟩
 | .div => ⟨.div,[]⟩
 | .ok (.Err err) => ⟨.ok (.Err err,s.world),[]⟩
 | .ok (.Ok variant) => common (commonFrame {s with parsed:=some variant}) s.world
#print code
#print observation
end NLM_Auth064Code
