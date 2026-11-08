import NNH_PhysicalCarriers
import NNH_WeakTx2Inputs
import NNE_SelectedRoutes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostWeak241
open Aeneas Aeneas.Std Result NNH_HostCtx NNH_Libraries
open S2W_D189Wrappers

theorem reference {W Tx : Type} (c : Ctx W Tx) (V : RSL.TX2_241.V2Lib)
 (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D V (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (envOf c) ⟨.ret (.ok (),post),events⟩) :
 ∃ es, RSL.TX2_241.Ref L D V
  ⟨NND_Carrier.key CPH_Program.verifier,NNH_ModelCarrier.accounts (c.j.entry.second secondSizes),
   NND_Carrier.bytes c.j.data,(envOf c).clock⟩
  (envOf c) ⟨.ret (.ok ()),es⟩ := by
 have route := NNE_SelectedRoutes.second L D V VL P C _ _ _ _
  (NNE_EntryArgs.count c.j.entry 7 CPH_Program.verifier c.j.data) ref ⟨post,rfl⟩
 have r240 := RSL.TAS.ref213_asq8 route ref
 obtain ⟨xs,es1,es2,_,snaps,_,child,_⟩ := NNE_RslOk.second_ok L D V _ _ post (envOf c) events r240
 have snapEq := (NNE_SnapshotSequence.second NND_Carrier.error rfl c.j.entry 0
  (envOf c) xs post es1 snaps).1
 subst xs
 refine ⟨es2,?_⟩
 simpa only [NNE_EntryArgs.args,NNH_PhysicalCarriers.key,NNH_PhysicalCarriers.bytes,
  NNH_PhysicalCarriers.accounts] using child

def clock (env : RSL.Env) : S2W_ExtractionBoundary.Slot :=
 NND_Carrier.unreply NND_Carrier.unslot env.clock

theorem clock_reply (env : RSL.Env) :
 NND_Carrier.reply NND_Carrier.slot (clock env) = env.clock := by
 unfold clock
 cases env.clock <;> simp only [NND_Carrier.unreply,NND_Carrier.reply,
  NND_Carrier.slot_forth,NND_Carrier.error_forth]

theorem inputs {W Tx : Type} (c : Ctx W Tx) (V : RSL.TX2_241.V2Lib)
 (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D V (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (envOf c) ⟨.ret (.ok (),post),events⟩) :
 Nonempty (NNH_WeakTx2Inputs.Packet NNH_HostSeed.m0 (envOf c) c.fixed.indexError
  c.fixed.reservation V CPH_Program.verifier (c.j.entry.second secondSizes) c.j.data (clock (envOf c))) := by
 obtain ⟨es,child⟩ := reference c V post events ref
 apply NNH_WeakTx2Inputs.produce _ _ _ _ V CPH_Program.verifier _ c.j.data (clock (envOf c)) es
 simpa only [clock_reply] using child
#print axioms reference
#print axioms clock_reply
#print axioms inputs
end AspisR1.NNH_HostWeak241
end
