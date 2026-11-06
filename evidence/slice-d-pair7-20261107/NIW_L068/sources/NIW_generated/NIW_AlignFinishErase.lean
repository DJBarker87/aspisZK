import NIW_AlignFinishExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishErase
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIT_FinishComposition NIW_AlignFinishExecution Classical

theorem bind_ext {A B : Type} (call : Result (Reply A)) (f g : A → Result (Reply B))
 (same : ∀ x,f x=g x) : fullBind call f=fullBind call g :=
 congrArg (fullBind call) (funext same)

/-- Erasing the deterministic source observations yields the exact finish
source-shaped skeleton. Every called child law is applied internally. The
only supplied predicate is the retained SAME-call finish input domain. -/
theorem skeleton (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 (run r v p a).1=NIT_FinishSkeleton.run r v p a := by
 have ca0 := (NIG_FinishAlpha.selected proof v p a domain 0#usize (by decide)).2
 have ca1 := (NIG_FinishAlpha.selected proof v p a domain 1#usize (by decide)).2
 rw [run,erase_observe,NIT_FinishSkeleton.run,
  ←NHT_RoundPacket.source r v.round0 _ p.claim 0#usize ca0 (by decide)]
 apply bind_ext
 intro first
 rw [erase_observe,←NHT_RoundPacket.source r v.round1 _ first 1#usize ca1 (by decide)]
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
   by_cases different : value≠claim
   · simp only [different,ite_true,done]
   · simp only [different,ite_false,erase_observe]
     apply bind_ext
     intro actual
     rfl

theorem source (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=
 (run r v p a).1 :=
 (NIT_FinishSkeleton.source r proof v p a domain).trans (skeleton r proof v p a domain).symm

#print axioms bind_ext
#print axioms skeleton
#print axioms source
end AspisR1.NIW_AlignFinishErase
