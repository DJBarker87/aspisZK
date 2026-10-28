import NCE_OuterCuts
import NCE_CarrierEffects
import NCE_CohortObservation

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_OuterObservation
open Aeneas Aeneas.Std NCE_OpeningCuts NCE_CarrierEffects
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def lifted (slot : NCE_FirstFailure.Slot) (batch : Nat) : NCE_OuterCuts.Child :=
  fun kind s => bind (annotate (fun _ out => out.2) s (slot batch kind s.scratch))
    fun out => .done (out.1.1,out.2)

def sequence (child : NCE_OuterCuts.Child) : List Nat → Carrier → Program Bytes State (Option Nat × Carrier)
  | [],s => .done (none,s)
  | kind::rest,s => bind (child kind s) fun out =>
      if out.1 then sequence child rest out.2 else .done (some kind,out.2)

/-- The carrier annotation retains chronological replies before every child
continuation. Its observer adds no independent source execution. -/
theorem lifted_eval (H : Bytes → State) (slot : NCE_FirstFailure.Slot) (batch kind : Nat) (s : Carrier) :
    eval H (lifted slot batch kind s) =
      let out := eval H (slot batch kind s.scratch)
      (out.1,(out.2.1,{s with scratch:=out.2.2,log:=s.log++out.1})) := by
  simp only [lifted,eval_bind,annotate_eval,eval,List.append_nil]

/-- All-outcome first-error observation on one initial Prepared/proof/scratch/
log. Subsequent child inputs are the preceding actual returned carrier. -/
theorem sequence_observation (H : Bytes → State) (slot : NCE_FirstFailure.Slot)
    (batch : Nat) (kinds : List Nat) (s : Carrier) :
    eval H (sequence (lifted slot batch) kinds s) =
      let out := NCE_FirstFailure.observe H slot (kinds.map (fun kind => (batch,kind))) s.scratch
      (out.1,(out.2.1.map Prod.snd,{s with scratch:=out.2.2,log:=s.log++out.1})) := by
  induction kinds generalizing s with
  | nil => simp only [sequence,eval,List.map_nil,NCE_FirstFailure.observe,Option.map_none,List.append_nil]
  | cons kind rest ih =>
    simp only [sequence,eval_bind,lifted_eval,List.map_cons,NCE_FirstFailure.observe]
    cases returned : eval H (slot batch kind s.scratch) with
    | mk log out =>
      rcases out with ⟨accepted,after⟩
      cases accepted with
      | false => simp only [Bool.false_eq_true,if_false,eval,List.append_nil,Option.map_some]
      | true => simp only [if_true,ih,List.append_assoc]

/-- Consume only the existing native dispatch/return fragment for the outer
three-call control. This is CONTROL, not a native proof of any child. -/
theorem control (H : Bytes → State) (child : NCE_OuterCuts.Child)
    (start : NCE_OuterCuts.Start) (after0 after1 : NCE_OuterCuts.Continue) (finish : NCE_OuterCuts.Finish)
    (cut : NCE_OuterCuts.NCE_Native_ThreeTrees start after0 after1 finish) (s : Carrier) :
    eval H (NCE_OuterCuts.program start after0 after1 finish child s) =
      eval H (sequence child [0,1,2] s) := by
  rw [NCE_OuterCuts.observation start after0 after1 finish cut H child s]
  simp only [sequence,eval_bind]
  cases first : (eval H (child 0 s)).2.1 <;>
    simp only [first,Bool.false_eq_true,if_true,if_false,eval_bind,eval,List.append_nil,List.append_assoc]
  all_goals
    cases second : (eval H (child 1 (eval H (child 0 s)).2.2)).2.1 <;>
      simp only [second,Bool.false_eq_true,if_true,if_false,eval_bind,eval,List.append_nil,List.append_assoc]
  all_goals
    cases third : (eval H (child 2 (eval H (child 1 (eval H (child 0 s)).2.2)).2.2)).2.1 <;>
      simp only [third,Bool.false_eq_true,if_true,if_false,eval_bind,eval,List.append_nil,List.append_assoc]

#print axioms lifted_eval
#print axioms sequence_observation
#print axioms control
end AspisR1.NCM_OuterObservation
end
