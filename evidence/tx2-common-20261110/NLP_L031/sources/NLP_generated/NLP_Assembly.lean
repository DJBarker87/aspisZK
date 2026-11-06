import NLP_NativeFold
import NLP_C04All
import NLP_C04Effects
import NLP_C01
set_option autoImplicit false
noncomputable section
namespace NLP_Assembly
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved NLB_Parent
open AspisV8R19.DuplexFrames
/-- Strongest assembled support. Explicit allocator/ABI/query cuts are STILL
auxiliary inputs, so this is NOT a TX2:065 row root. No child Result, success,
endpoint, packet, Merkle dictionary, or Resume dictionary is hypothesized. -/
theorem installed (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (publicLen : pub.val.length≤1880)
 (root0Input : NLP_InputDomain.Root0 ck proof)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr (NLP_NativeMerkle.action H) d pub proof ck hash observe) :
 (let w:=flushWindow (queryWindow (window rr fr loc
  (NLB_ResumePacket.action NLP_ResumeInstall.native wr) (NLP_NativeMerkle.action H) d hash) observe)
  let p:=NKE_CommonProgram.run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none
  G w p []=.done (NJJ_Common.run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none)
   (run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none).events) ∧
 NKE_EventAll.Holds (NLP_C04All.Clause H)
  (run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none) ∧
 NKU_CallerScope.Inputs (NKU.initial ⟨ck,proof,pub,wr⟩).frame :=
 ⟨NLP_NativeFold.installed H wr rr fr loc d pub proof ck hash len observe cuts [],
  NLP_C04All.source H wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash len root0Input,
  NLP_ResumeInstall.scope wr ck proof pub len publicLen⟩
set_option pp.proofs false
#print installed
#print axioms installed
end NLP_Assembly
