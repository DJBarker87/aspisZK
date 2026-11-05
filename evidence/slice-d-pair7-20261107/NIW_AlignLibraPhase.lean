import NIW_AlignLibraSource
import NIW_AlignFinalPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibraPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

structure Log where
 steps : List NIW_AlignLibraCollect.Event
 final : Option NIW_AlignFinalPhase.Log

def run (f : Ref (Slice U8)) (weights : Powers) (parts : Parts) (kappa : E) : Result NR × Log :=
 let observed := NIW_AlignLibraCollect.collect f weights 5 ({start:=0#usize,«end»:=4#usize},parts)
 match observed.1 with
 | fail err => (fail err,⟨observed.2,none⟩)
 | div => (div,⟨observed.2,none⟩)
 | ok after =>
  let final := NIW_AlignFinalPhase.run after kappa
  (final.1,⟨observed.2,some final.2⟩)

theorem trace (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (weights : Powers) (cw : canonical weights) (parts : Parts) (cp : canonical parts)
 (kappa : E) (ck : canonE kappa) :
 NIT_TailPhases.Libra f weights parts kappa (run f weights parts kappa).1 := by
 have observed := NIW_AlignLibraCollect.trace f size weights cw 5
  ({start:=0#usize,«end»:=4#usize},parts) rfl (by change (0:Nat)≤4;omega) cp
  (by change (4:Nat)-0<5;omega)
 cases result : (NIW_AlignLibraCollect.collect f weights 5 ({start:=0#usize,«end»:=4#usize},parts)).1 with
 | fail err =>
  simp only [result] at observed
  simp only [run,result]
  exact .failed err observed.1
 | div =>
  simp only [result] at observed
  simp only [run,result]
  exact .diverged observed.1
 | ok after =>
  simp only [result] at observed
  simp only [run,result]
  exact .returned after _ observed.1 (NIW_AlignFinalPhase.trace after kappa observed.2 ck)

theorem source (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (weights : Powers) (cw : canonical weights) (parts : Parts) (cp : canonical parts)
 (kappa : E) (ck : canonE kappa) :
 NIT_TailPhases.libra f weights parts kappa=(run f weights parts kappa).1 :=
 NIT_TailPhases.libra_interpreted f weights parts kappa _ (trace f size weights cw parts cp kappa ck)

#print axioms trace
#print axioms source
end AspisR1.NIW_AlignLibraPhase
