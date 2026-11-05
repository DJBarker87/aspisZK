import NIW_AlignGroupObservation
import NIW_AlignLibraPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignGroupPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_TailCuts NIT_PairControl

structure Log where
 group : Result E
 updateAndFactor : Option (Result (Parts×Powers×Tail))
 tail : Option NIW_AlignLibraPhase.Log

def run (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts) (kappa : E) : Result NR × Log :=
 let group := FIo_Native.weights.grouped_inactive_pair w.value f.value low.value
 match group with
 | fail err => (fail err,⟨group,none,none⟩)
 | div => (div,⟨group,none,none⟩)
 | ok value =>
  let payload := NIW_AlignGroupObservation.afterGroup w f low ap0 ap1 parts value
  match payload with
  | fail err => (fail err,⟨group,some payload,none⟩)
  | div => (div,⟨group,some payload,none⟩)
  | ok (after,weights,_) =>
   let tail := NIW_AlignLibraPhase.run f weights after kappa
   (tail.1,⟨group,some payload,some tail.2⟩)

theorem trace (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts) (kappa : E)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (cl : canonical low.value) (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (ck : canonE kappa) :
 NIT_TailPhases.Group w f low ap0 ap1 parts kappa (run w f low ap0 ap1 parts kappa).1 := by
 cases groupCall : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value with
 | fail err =>
  have model := (NHX_GroupPacket.source w.value f.value low.value s2 size).symm.trans groupCall
  simp only [run,groupCall]
  exact .failed err model
 | div =>
  have model := (NHX_GroupPacket.source w.value f.value low.value s2 size).symm.trans groupCall
  simp only [run,groupCall]
  exact .diverged model
 | ok value =>
  have obs := NIW_AlignGroupObservation.returned w f low ap0 ap1 parts s2 size cl c0 c1 ce cp value groupCall
  cases payload : NIW_AlignGroupObservation.afterGroup w f low ap0 ap1 parts value with
  | fail err => simp only [payload,NIW_AlignFieldReply.Produced] at obs
  | div => simp only [payload,NIW_AlignFieldReply.Produced] at obs
  | ok result =>
   rcases result with ⟨after,weights,log⟩
   simp only [payload,NIW_AlignFieldReply.Produced] at obs
   rcases obs with ⟨cut,ca,cw,groupModel,factorModel⟩
   have same : weights=log.libra_reply := by
    rcases cut with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,same⟩
    exact same
   have tail : NIT_TailPhases.Libra f log.libra_reply after kappa
    (NIW_AlignLibraPhase.run f weights after kappa).1 := by
    rw [←same]
    exact NIW_AlignLibraPhase.trace f size weights cw after ca kappa ck
   simp only [run,groupCall,payload]
   exact .returned log after _ cut groupModel factorModel tail

theorem source (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts) (kappa : E)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (cl : canonical low.value) (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (ck : canonE kappa) :
 NIT_TailPhases.group w f low ap0 ap1 parts kappa=(run w f low ap0 ap1 parts kappa).1 :=
 NIT_TailPhases.group_interpreted w f low ap0 ap1 parts kappa s2 size ce _
  (trace w f low ap0 ap1 parts kappa s2 size cl c0 c1 ce cp ck)

#print axioms trace
#print axioms source
end AspisR1.NIW_AlignGroupPhase
