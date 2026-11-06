import NLC_Step_extra28
import NLC_Step_addExtra
import NLC_Step_terminalGuard
import NLC_Step_mark4
import NLC_Step_stateBefore
import NLC_Step_record25b
import NLC_Step_circle0
import NLC_Step_record26a
import NLC_ReadyBase
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_extra28 {H : Type} (s : State H) (atSite : s.next = .extra28) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_extra28 s atSite]
 unfold window_extra28
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_extra28

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_addExtra {H : Type} (s : State H) (atSite : s.next = .addExtra) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_addExtra s atSite]
 unfold window_addExtra
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_addExtra

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_terminalGuard {H : Type} (s : State H) (atSite : s.next = .terminalGuard) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_terminalGuard s atSite]
 unfold window_terminalGuard
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_terminalGuard

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_mark4 {H : Type} (s : State H) (atSite : s.next = .mark4) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_mark4 s atSite]
 unfold window_mark4
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_mark4

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_stateBefore {H : Type} (s : State H) (atSite : s.next = .stateBefore) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_stateBefore s atSite]
 unfold window_stateBefore
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_stateBefore

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_record25b {H : Type} (s : State H) (atSite : s.next = .record25b) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_record25b s atSite]
 unfold window_record25b
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_record25b

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_circle0 {H : Type} (s : State H) (atSite : s.next = .circle0) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_circle0 s atSite]
 unfold window_circle0
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_circle0

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_record26a {H : Type} (s : State H) (atSite : s.next = .record26a) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_record26a s atSite]
 unfold window_record26a
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_record26a
end AspisR1.NLC_Finish
end
