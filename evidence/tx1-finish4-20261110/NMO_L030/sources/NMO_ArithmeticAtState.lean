import NMO_ArithmeticValue
import NMO_MaskStored
import NMO_MulAtState
import NMO_ExtraStored
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ArithmeticAtState
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- The complete arithmetic frame is built from ONE reached parent. Every
canonicality clause comes from actual source producers, never a supplied
successful child or an independent completed array. Native association of
this frame with the scalar cuts remains NMO-F1. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (atSite : s.machine.next=.multiply) :
 ∃ (f : NLU_FieldLog.Frame) (words : Words),
 s.machine.locals.terminal=some f.terminal ∧ s.machine.locals.mask=some f.mask ∧
 s.machine.locals.extra=some words ∧ f.eta=input.challenges.eta ∧
 f.extra=NKQ_ArrayWindows.cell words 28 (by decide) ∧
 ∃ replies : NLU_FieldLog.Replies,NLU_Arithmetic.code input.reservation f=ok replies.total ∧
 JFv_RoundArithmetic.Canonical replies.total ∧
 FIv_NativeValue.decode (FIq_Carriers.toQ replies.total)=
  (FIv_NativeValue.decode (FIq_Carriers.toQ f.mask)+
   FIv_NativeValue.decode (FIq_Carriers.toQ f.eta)*FIv_NativeValue.decode (FIq_Carriers.toQ f.terminal))+
  FIv_NativeValue.decode (FIq_Carriers.toQ f.extra) := by
 have ready:=(NLU.reachable_invariant input s reached).1.1
 have maskInit : s.machine.locals.mask.isSome=true:=ready.2.2.2.2.2.2.2.2.2.1 (by rw [atSite];decide)
 have extraInit : s.machine.locals.extra.isSome=true:=ready.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [atSite];decide)
 obtain ⟨mask,maskStored⟩:=NMC_Records.some_slot s.machine.locals.mask maskInit
 obtain ⟨words,extraStored⟩:=NMC_Records.some_slot s.machine.locals.extra extraInit
 obtain ⟨terminal,terminalStored,he,ht⟩:=NMO_MulAtState.operands native cut token frame input domain s reached atSite
 have hm:=(NKQ_CanonicalBridge.canonical mask).mpr ((NMO_MaskStored.reachable native cut token frame input domain s reached) mask maskStored)
 let extra:=NKQ_ArrayWindows.cell words 28 (by decide)
 have hx : JFv_RoundArithmetic.Canonical extra:=(NMO_ExtraStored.reachable input s reached) words extraStored extra (List.getElem_mem _)
 let f : NLU_FieldLog.Frame:=⟨input.challenges.eta,terminal,mask,extra⟩
 obtain ⟨replies,code,_,_,canonical,value⟩:=NMO_ArithmeticValue.source input.reservation f he ht hm hx
 exact ⟨f,words,terminalStored,maskStored,extraStored,rfl,rfl,replies,code,canonical,value⟩
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NMO_ArithmeticAtState
end
