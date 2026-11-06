import NIW_AlignCommonSource
import NIW_AlignPartialPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignSharedPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

structure Log where
 common : List NIW_AlignCommonCollect.Event
 partialReply : Option (Result RP)
 tail : Option NIW_AlignPartialPhase.Log

def run (c : Context) (parts : Parts) : Result NR × Log :=
 let common := NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)
 match common.1 with
 | fail err => (fail err,⟨common.2,none,none⟩)
 | div => (div,⟨common.2,none,none⟩)
 | ok (owner,cells) =>
  let partialReply := FIo_Native.weights.shared_partials c.f.value cells
  match partialReply with
  | fail err => (fail err,⟨common.2,some partialReply,none⟩)
  | div => (div,⟨common.2,some partialReply,none⟩)
  | ok reply =>
   let tail := NIW_AlignPartialPhase.run c ⟨c.w.address,owner⟩ parts reply
   (tail.1,⟨common.2,some partialReply,some tail.2⟩)

theorem trace (c : Context) (parts : Parts)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) :
 NIT_SharedChain.Shared c parts (run c parts).1 := by
 have cz : NHI_CellCanon.array (Array.repeat 16#usize NHX_FilledZero.zeroQ) := by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  exact hx.2 ▸ NHX_FilledZero.zero_canonical
 have observed := (NIW_AlignCommonSource.source c.w.value domain.factors _ cz).2
 cases result : (NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | div => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | ok value =>
  rcases value with ⟨owner,cells⟩
  simp only [result,NIW_AlignFieldReply.Produced] at observed
  have same := observed.2.1
  dsimp only at same
  subst owner
  cases partialCall : FIo_Native.weights.shared_partials c.f.value cells with
  | fail err =>
   simp only [run,result,partialCall]
   exact .failed c.w.value cells err observed.1 partialCall
  | div =>
   simp only [run,result,partialCall]
   exact .diverged c.w.value cells observed.1 partialCall
  | ok reply =>
   simp only [run,result,partialCall]
   exact .returned c.w.value cells reply _ observed.1 partialCall
    (NIW_AlignPartialPhase.trace c c.w parts reply domain.s2
     (NIT_PairDomain.message_size _ _ _ _ domain) domain.factors domain.extra c0 c1 cp domain.kappa)

#print axioms trace
end AspisR1.NIW_AlignSharedPhase
