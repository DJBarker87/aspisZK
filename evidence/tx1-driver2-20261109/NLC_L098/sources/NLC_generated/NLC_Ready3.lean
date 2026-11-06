import NLC_Step_decode26
import NLC_Step_record26b
import NLC_Step_circle1
import NLC_Step_mark5
import NLC_Step_circleGuard
import NLC_Step_payload2
import NLC_Step_rootCopy
import NLC_Step_verified
import NLC_ReadyBase
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_decode26 {H : Type} (s : State H) (atSite : s.next = .decode26) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_decode26 s atSite]
 unfold window_decode26
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_decode26

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_record26b {H : Type} (s : State H) (atSite : s.next = .record26b) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_record26b s atSite]
 unfold window_record26b
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_record26b

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_circle1 {H : Type} (s : State H) (atSite : s.next = .circle1) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_circle1 s atSite]
 unfold window_circle1
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_circle1

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_mark5 {H : Type} (s : State H) (atSite : s.next = .mark5) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_mark5 s atSite]
 unfold window_mark5
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_mark5

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_circleGuard {H : Type} (s : State H) (atSite : s.next = .circleGuard) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_circleGuard s atSite]
 unfold window_circleGuard
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_circleGuard

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_payload2 {H : Type} (s : State H) (atSite : s.next = .payload2) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_payload2 s atSite]
 unfold window_payload2
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_payload2

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_rootCopy {H : Type} (s : State H) (atSite : s.next = .rootCopy) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_rootCopy s atSite]
 unfold window_rootCopy
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_rootCopy

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_verified {H : Type} (s : State H) (atSite : s.next = .verified) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_verified s atSite]
 unfold window_verified
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_verified
end AspisR1.NLC_Finish
end
