import NIW_AlignLowCollect
import NIW_AlignGroupPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignTailPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

structure Log where
 low : List NIW_AlignLowCollect.Event
 group : Option NIW_AlignGroupPhase.Log

def run (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) (lowAddress : Nat) : Result NR × Log :=
 let observed := NIW_AlignLowCollect.collect ap0.value ap1.value 17
  ({start:=0#usize,«end»:=16#usize},NIT_TailChain.zero)
 match observed.1 with
 | fail err => (fail err,⟨observed.2,none⟩)
 | div => (div,⟨observed.2,none⟩)
 | ok cells =>
  let group := NIW_AlignGroupPhase.run w f ⟨lowAddress,cells⟩ ap0 ap1 parts kappa
  (group.1,⟨observed.2,some group.2⟩)

theorem trace (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) (lowAddress : Nat)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (ck : canonE kappa) :
 NIT_TailChain.Trace w f ap0 ap1 parts kappa lowAddress (run w f ap0 ap1 parts kappa lowAddress).1 := by
 have observed := NIW_AlignLowCollect.trace ap0.value ap1.value c0 c1 17
  ({start:=0#usize,«end»:=16#usize},NIT_TailChain.zero) rfl (by change (0:Nat)≤16;omega)
  NIT_TailChain.zero_canonical (by change (16:Nat)-0<17;omega)
 cases result : (NIW_AlignLowCollect.collect ap0.value ap1.value 17
  ({start:=0#usize,«end»:=16#usize},NIT_TailChain.zero)).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | div => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | ok cells =>
  simp only [result,NIW_AlignFieldReply.Produced] at observed
  simp only [run,result]
  exact .low cells _ observed.1
   (NIW_AlignGroupPhase.trace w f ⟨lowAddress,cells⟩ ap0 ap1 parts kappa s2 size observed.2 c0 c1 ce cp ck)

theorem source (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) (lowAddress : Nat)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (ck : canonE kappa) :
 NIT_TailChain.sourceTail w.value f.value ap0.value ap1.value parts kappa=
 (run w f ap0 ap1 parts kappa lowAddress).1 :=
 (NIT_TailChain.source w f ap0 ap1 parts kappa lowAddress s2).trans
  (NIT_TailChain.interpreted w f ap0 ap1 parts kappa lowAddress s2 size ce _
   (trace w f ap0 ap1 parts kappa lowAddress s2 size c0 c1 ce cp ck))

#print axioms trace
#print axioms source
end AspisR1.NIW_AlignTailPhase
