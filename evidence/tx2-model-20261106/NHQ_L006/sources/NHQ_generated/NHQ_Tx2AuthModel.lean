import NHQ_Tx2CommonModel
set_option autoImplicit false
noncomputable section
namespace NHQ_Tx2AuthModel
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := core.result.Result A verifier.Error
variable {H : Type}
variable (ops : Ops) (digest : aspis_core.digest.Digest32 H)
variable (pub proof checkpoint : Slice U8) (hash : H)
variable (obs : Option (verifier.Phase → Result Unit))

def afterShape (reply : R transport.Variant) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue _ =>
   ops.op13 obs verifier.Phase.Parsed
   NHQ_Tx2CommonModel.run ops digest pub proof checkpoint hash obs
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Unit (core.convert.FromSame verifier.Error) residual

def run : Result (R Unit) := do
 let reply ← ops.op3 proof
 afterShape ops digest pub proof checkpoint hash obs reply

theorem source : verifier.candidate.tx2_authenticated ops digest pub proof checkpoint hash obs =
 run ops digest pub proof checkpoint hash obs := by rfl

theorem parsed (variant : transport.Variant) (shape_packet : ops.op3 proof=ok (.Ok variant)) :
 run ops digest pub proof checkpoint hash obs =
 (do ops.op13 obs verifier.Phase.Parsed
     NHQ_Tx2CommonModel.run ops digest pub proof checkpoint hash obs) := by
 unfold run
 rw [shape_packet]
 rfl

theorem shape_error (error : verifier.Error) (shape_packet : ops.op3 proof=ok (.Err error)) :
 run ops digest pub proof checkpoint hash obs = ok (.Err error) := by
 unfold run
 rw [shape_packet]
 rfl
#print axioms source
#print axioms parsed
#print axioms shape_error
end NHQ_Tx2AuthModel
