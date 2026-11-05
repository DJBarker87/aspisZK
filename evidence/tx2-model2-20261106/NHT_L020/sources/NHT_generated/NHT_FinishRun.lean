import NHT_FinishChain
import NHT_RoundPacket
set_option autoImplicit false
noncomputable section
namespace NHT_FinishRun
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl NHQ_FinishRelationModel
open NHT_FinishChain
variable {W : Type}

def afterFirst (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W) (alpha1 : E)
 (reply : R E) : Result (R Unit) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
 match cf with
 | .Continue first =>
   let last ← NHT_RoundPacket.packet v.round1 alpha1 first
   afterRound ops v p a obs ws pair 2#usize last
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame verifier.Error) residual

theorem first_frame (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W) (alpha1 : E)
 (folds : ops.op6 p.variant=ok 2#usize)
 (index1 : Array.index_usize p.alpha 1#usize=ok alpha1)
 (round1 : ∀ claim, ops.op5 v.round1 alpha1 claim 1#usize=
   NHT_RoundPacket.packet v.round1 alpha1 claim)
 (next : ∀ reply, afterRoundReply ops v p a obs 2#usize reply =
   afterRound ops v p a obs ws pair 2#usize reply)
 (reply : R E) :
 afterRound0 ops v p a obs reply = afterFirst ops v p a obs ws pair alpha1 reply := by
 cases reply with
 | Err e => rfl
 | Ok first =>
   unfold afterRound0 afterFirst
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,folds,index1,↓reduceIte]
   rw [round1 first]
   apply NHT_BindOn.reached
   intro r _
   exact next r

def run (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W) (alpha0 alpha1 : E) : Result (R Unit) := do
 let reply ← NHT_RoundPacket.packet v.round0 alpha0 p.claim
 afterFirst ops v p a obs ws pair alpha1 reply

theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
 (ws : Slice NHE_DotBody.NQ) (pair : PairPacket W) (alpha0 alpha1 : E)
 (index0 : Array.index_usize p.alpha 0#usize=ok alpha0)
 (round0 : ops.op5 v.round0 alpha0 p.claim 0#usize =
   NHT_RoundPacket.packet v.round0 alpha0 p.claim)
 (first : ∀ reply, afterRound0 ops v p a obs reply=
   afterFirst ops v p a obs ws pair alpha1 reply) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs =
 run ops v p a obs ws pair alpha0 alpha1 := by
 rw [NHQ_FinishRelationModel.source]
 unfold NHQ_FinishRelationModel.staged run
 rw [index0,bind_tc_ok,round0]
 apply NHT_BindOn.reached
 intro reply _
 exact first reply
#print axioms first_frame
#print axioms source
end NHT_FinishRun
