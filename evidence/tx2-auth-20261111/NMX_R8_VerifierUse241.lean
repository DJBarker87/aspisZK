import NMX_R8_Emit241
import NMX_R8_MapBind
set_option autoImplicit false
noncomputable section
namespace NMX_R8_VerifierUse241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev V := LIBB_V2Star.library

def source (s : LIBB_PoolCarriers.Statement) (pub proof ck : Slice U8) :=
 RSL.Spec.bind (NMX_R7_VerifierSource241.meaning pub proof ck) fun r =>
 NMS_R2N_RawTry.literal
  (NMS_Effect241.mapError r (NMS_R2ErrorSource.callback V NMX_R7_Error241.embed))
  (fun _ => NMX_R8_Emit241.meaning s)

theorem full (s : LIBB_PoolCarriers.Statement) (pub proof ck : Slice U8) :
 Simulates (NMS_R2N_RSLError.reply id) (source s pub proof ck)
  (RSL.RS.bind (RSL.RS.lift (V.tx2auth (NMS_R2N_RSLScalars.bytes pub)
    (NMS_R2N_RSLScalars.bytes proof) (NMS_R2N_RSLScalars.bytes ck))) fun r =>
   RSL.RS.seq (RSL.TX2_241.mapVErr V r) (LIBB_PoolLib.library.emitResult s)) := by
 unfold source
 rw [NMX_R8_MapBind.lift_bind]
 apply NMS_R2N_Interpreted.bind (NMS_R2ErrorSource.verifierReply V NMX_R7_Error241.embed)
  (NMS_R2N_RSLError.reply id)
 · exact NMX_R7_VerifierSource241.full pub proof ck
 · intro r
   apply NMS_R2N_RawTry.simulates id id
   · exact NMX_R7_Error241.full r
   · intro unit
     exact NMX_R8_Emit241.full s
#print axioms full
end NMX_R8_VerifierUse241
end
