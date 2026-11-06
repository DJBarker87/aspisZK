import NLC_Step_rounds
import NLC_Step_mark2
import NLC_Step_claims
import NLC_Step_original
import NLC_Step_terminal
import NLC_Step_mapPublic
import NLC_Step_mark3
import NLC_Step_lowArray
import NLC_ReadyBase
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_rounds {H : Type} (s : State H) (atSite : s.next = .rounds) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_rounds s atSite]
 unfold window_rounds
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_rounds

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_mark2 {H : Type} (s : State H) (atSite : s.next = .mark2) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_mark2 s atSite]
 unfold window_mark2
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_mark2

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_claims {H : Type} (s : State H) (atSite : s.next = .claims) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_claims s atSite]
 unfold window_claims
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_claims

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_original {H : Type} (s : State H) (atSite : s.next = .original) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_original s atSite]
 unfold window_original
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_original

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_terminal {H : Type} (s : State H) (atSite : s.next = .terminal) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_terminal s atSite]
 unfold window_terminal
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_terminal

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_mapPublic {H : Type} (s : State H) (atSite : s.next = .mapPublic) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_mapPublic s atSite]
 unfold window_mapPublic
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_mapPublic

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_mark3 {H : Type} (s : State H) (atSite : s.next = .mark3) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_mark3 s atSite]
 unfold window_mark3
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_mark3

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_lowArray {H : Type} (s : State H) (atSite : s.next = .lowArray) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_lowArray s atSite]
 unfold window_lowArray
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_lowArray
end AspisR1.NLC_Finish
end
