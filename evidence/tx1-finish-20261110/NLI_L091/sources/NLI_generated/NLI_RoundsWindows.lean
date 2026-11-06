import NLI_RoundsCarry
import NJG_RoundsCompose
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_RoundsWindows
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_NativeCuts
/-- Universal fields of ONE return, matching the NLI running/alpha/transcript
windows and full Err/tag assertions. No coordinate selects a new execution. -/
def Windows (native : NLI_RoundsCarry.Native) : Prop :=
 ∀ reply (k : Fin 10) (z : Fin 32) (limb : Fin 4),
 match reply,native reply with
 | .Err e,.Err out=>out=e
 | .Ok (running,alpha,state,next),.Ok (r,a,t,n)=>
   word r limb=word running limb ∧ word (cell a k) limb=word (cell alpha k) limb ∧
   cell t z=cell state z ∧ n=next
 | _,_=>False
/-- Reuse the checked generic Result extensionality law. Unused template
fields below are algebraic parameters only, never a native pre-state or an
independently chosen source execution. -/
theorem complete (native : NLI_RoundsCarry.Native) (windows : Windows native) :
 NLI_RoundsCarry.Cut native := by
 intro reply
 let template : RoundsPre := {
  prefixToken:=0,round:=0,alpha:=Array.repeat 10#usize aspis_core.field.QM31.ZERO,
  running:=aspis_core.field.QM31.ZERO,state:=Array.repeat 32#usize 0#u8,
  next:=0#u8,reply:=reply,count:=0,frame:=0 }
 apply NJG_RoundsCompose.complete template (native reply) 0
 intro k z limb
 exact ⟨(by change 0<255;decide),rfl,windows reply k z limb⟩
#print axioms complete
end AspisR1.NLI_RoundsWindows
end
