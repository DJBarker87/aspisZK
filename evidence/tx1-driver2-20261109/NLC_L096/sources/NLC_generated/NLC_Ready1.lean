import NLC_Step_highArray
import NLC_Step_blind
import NLC_Step_alpha
import NLC_Step_mask
import NLC_Step_record25a
import NLC_Step_decode25
import NLC_Step_multiply
import NLC_Step_addMask
import NLC_ReadyBase
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_highArray {H : Type} (s : State H) (atSite : s.next = .highArray) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_highArray s atSite]
 unfold window_highArray
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_highArray

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_blind {H : Type} (s : State H) (atSite : s.next = .blind) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_blind s atSite]
 unfold window_blind
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_blind

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_alpha {H : Type} (s : State H) (atSite : s.next = .alpha) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_alpha s atSite]
 unfold window_alpha
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_alpha

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_mask {H : Type} (s : State H) (atSite : s.next = .mask) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_mask s atSite]
 unfold window_mask
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_mask

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_record25a {H : Type} (s : State H) (atSite : s.next = .record25a) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_record25a s atSite]
 unfold window_record25a
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_record25a

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_decode25 {H : Type} (s : State H) (atSite : s.next = .decode25) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_decode25 s atSite]
 unfold window_decode25
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_decode25

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_multiply {H : Type} (s : State H) (atSite : s.next = .multiply) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_multiply s atSite]
 unfold window_multiply
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_multiply

/-- Preservation of initialized slots for every possible source reply. -/
theorem ready_addMask {H : Type} (s : State H) (atSite : s.next = .addMask) (before : Ready s) :
 AllLeaves ReadyPost (step s) := by
 rw [step_addMask s atSite]
 unfold window_addMask
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (apply ready_returned; intro)
 | (change Ready _; simp_all [Ready,put,setNext,rank])
 | (change True; trivial)
 | split
#print axioms ready_addMask
end AspisR1.NLC_Finish
end
