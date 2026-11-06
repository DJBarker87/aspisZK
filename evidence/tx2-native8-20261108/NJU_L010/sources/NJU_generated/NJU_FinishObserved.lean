import NJU_FinishCore
import NIW_AlignFinishExecution
set_option autoImplicit false
noncomputable section
namespace NJU_FinishObserved
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition NIW_AlignFinishExecution Classical

theorem bind_ext {A B : Type} (call : Result (Reply A)) (f g : A → Result (Reply B))
 (same : ∀ x,f x=g x) : fullBind call f=fullBind call g :=
 congrArg (fullBind call) (funext same)

/-- Generalization of the existing NIW source-observation erasure to arbitrary
raw bytes. Only the two intrinsic alpha canonicality facts are used in this
step. No native pair claim or supplemental closure is inferred. -/
theorem skeleton (r : NP6_StdModel.Reservation)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (core : NJU_FinishCore.Holds p a) :
 (run r v p a).1=NIT_FinishSkeleton.run r v p a := by
 have ca0 := (NJU_FinishCore.selected p a core 0#usize (by decide)).2
 have ca1 := (NJU_FinishCore.selected p a core 1#usize (by decide)).2
 have law0 : Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
   v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim 0#usize=
   NHT_RoundPacket.packet v.round0 (NIG_FinishAlpha.alpha p 0 (by decide)) p.claim :=
  (NHT_RoundPacket.source r v.round0 _ p.claim 0#usize ca0 (by decide)).symm
 rw [run,erase_observe,NIT_FinishSkeleton.run,law0]
 apply bind_ext
 intro first
 have law1 : Stage2Finish.verifier.finishRelationRoundWithOps (IDa_Deployed.finish r)
   v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first 1#usize=
   NHT_RoundPacket.packet v.round1 (NIG_FinishAlpha.alpha p 1 (by decide)) first :=
  (NHT_RoundPacket.source r v.round1 _ first 1#usize ca1 (by decide)).symm
 rw [erase_observe,law1]
 apply bind_ext
 intro claim
 rw [erase_observe,NIG_FinishExport.NHM_new]
 apply bind_ext
 intro owner
 cases range : core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice FE)) p.alpha {«end»:=2#usize} with
 | fail e => simp only [range];rfl
 | div => simp only [range];rfl
 | ok alpha =>
  simp only [range,bind_tc_ok]
  rw [erase_observe,NIG_PairExport.source]
  unfold fullBind
  apply NIT_PairControl.bind_ext
  intro reply
  cases reply with
  | Err e => rfl
  | Ok value =>
   simp only [NIT_FinishTail.afterPair,fullBind,bind_tc_ok]
   simp only [done]
   split_ifs
   · rfl
   · rw [erase_observe]
     apply bind_ext
     intro actual
     rfl

theorem source (r : NP6_StdModel.Reservation)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (core : NJU_FinishCore.Holds p a) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 (run r v p a).1 :=
 (NJU_FinishCore.source r v p a core).trans (skeleton r v p a core).symm

#print source
#print axioms bind_ext
#print axioms skeleton
#print axioms source
end NJU_FinishObserved
