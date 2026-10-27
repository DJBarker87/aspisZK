import F3U_Joint
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Averaging
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.CausalFirstHitUnionBound

theorem charge {A B C : Type} (p : Program Bytes State A) (q : Program Bytes State B)
    (r : Program Bytes State C) (f : View Bytes State A → Rat) (g : View Bytes State B → Rat)
    (event : View Bytes State C → Prop)
    (pointwise : ∀ H : Bytes → State,f (eval H p)≤g (eval H q)+indicator (event (eval H r))) :
    lazyMean p emptyTable f≤lazyMean q emptyTable g+
      lazyMean r emptyTable (fun v=>indicator (event v)) := by
  let joint := F3U_Joint.program p q r
  have lp : lazyMean p emptyTable f=lazyMean joint emptyTable (fun v=>f v.2.1) := by
    apply OracleProgramLawExt.lazyMean_eq_of_eval
    intro H
    rw [F3U_Joint.output]
  have lq : lazyMean q emptyTable g=lazyMean joint emptyTable (fun v=>g v.2.2.1) := by
    apply OracleProgramLawExt.lazyMean_eq_of_eval
    intro H
    rw [F3U_Joint.output]
  have lr : lazyMean r emptyTable (fun v=>indicator (event v))=
      lazyMean joint emptyTable (fun v=>indicator (event v.2.2.2)) := by
    apply OracleProgramLawExt.lazyMean_eq_of_eval
    intro H
    rw [F3U_Joint.output]
  rw [lp,lq,lr,←lazyMean_add]
  apply AllAddressFiatShamir.lazyMean_mono_of_eval
  intro H
  simpa only [joint,F3U_Joint.output] using pointwise H

#print axioms charge
end AspisR1.F3U_Averaging
end
