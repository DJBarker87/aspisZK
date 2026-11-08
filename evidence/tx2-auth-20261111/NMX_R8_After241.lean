import NMX_R8_AfterFactor241
import NMX_R8_Reads241
import NMX_R8_Indexes241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_After241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library
abbrev V := LIBB_V2Star.library

def model (v : RSL.TX2_242.Validated L) (accounts : List RSL.OwnedAccount) : RSL.RS Unit :=
 RSL.RS.bind (RSL.RS.index accounts 0) fun acc0 =>
 RSL.RS.bind acc0.data fun proof =>
 RSL.RS.bind (RSL.RS.index accounts 6) fun acc6 =>
 RSL.RS.bind acc6.data fun ck =>
 NMS_R2Replay241.afterReads L V NMX_R8_RelReplay241.verify v proof ck

theorem full (env : RSL.Env) (choices : NMX_R4_Authentication.Choices)
 (v : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (length : v.proof_length = 57607#usize) :
 Simulates (NMS_R2N_RSLError.reply id)
  (NMX_R8_Factor241.afterValidate (NMX_R8_Std241.ops env) (NMX_R8_Children241.grouped choices) v accounts)
  (model (NMX_R5_AfterAuth242.value v) (NMS_R2N_RSLPoolCarriers.accounts accounts)) := by
 rw [NMX_R8_AfterFactor241.factor]
 unfold NMX_R8_AfterFactor241.source model
 have zero : (0#usize).val = 0 := by scalar_tac
 have six : (6#usize).val = 6 := by scalar_tac
 apply NMX_R8_SimulatesPath.infallible NMS_R2N_RSLPoolCarriers.account (NMS_R2N_RSLError.reply id)
 · simpa only [zero] using NMX_R8_Indexes241.full accounts 0#usize
 · intro acc0
   apply NMS_R2N_RawTry.simulates NMS_R2N_RSLScalars.bytes id
   · exact NMS_R2GetterLink.full acc0
   · intro proof
     apply NMX_R8_SimulatesPath.infallible NMS_R2N_RSLPoolCarriers.account (NMS_R2N_RSLError.reply id)
     · simpa only [six] using NMX_R8_Indexes241.full accounts 6#usize
     · intro acc6
       apply NMS_R2N_RawTry.simulates NMS_R2N_RSLScalars.bytes id
       · exact NMS_R2GetterLink.full acc6
       · intro ck
         exact NMX_R8_Reads241.full env choices v proof ck length
#print axioms full
end NMX_R8_After241
end
