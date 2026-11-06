import NJF_SliceCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_CutEvaluation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl Classical
open NJF_SliceCuts

/-- A native post-window is consumed FORWARD, evaluated at its oracle replies.
Neither arbitrary raw log association nor a child endpoint equality is assumed. -/
theorem state (c : Context) (shared : Bool) (l : Replies) (args : Arguments)
 (scratch : Scratch) (parts : Parts) (out : RU) (events : Nat → Nat) (calls : Nat)
 (native : cut c shared l args scratch parts out events calls) :
 (out,scratch,parts)=(expected shared l,l.scratch,if enteredHigh shared l then l.highParts else l.parts) := by
 rcases native with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,result,_,_,hs,hp,_,_⟩
 rw [result,hs,hp]

/-- Exact full Result/state post is the G evaluator's post. Each word window is
lifted by finite-array extensionality; no selected oracle seed is used as the
child's entire post without the corrected full-footprint cut. -/
theorem evaluated (c : Context) (shared : Bool) (l : Replies) (args : Arguments)
 (scratch : Scratch) (parts : Parts) (out : RU) (events : Nat → Nat) (calls : Nat)
 (native : cut c shared l args scratch parts out events calls) :
 ok (out,scratch,parts)=(NJF_RegularCut.G shared (log c.w.value l)).1 := by
 rw [state c shared l args scratch parts out events calls native]
 rw [evaluator]

#print axioms state
#print axioms evaluated
end AspisR1.NJF_CutEvaluation
