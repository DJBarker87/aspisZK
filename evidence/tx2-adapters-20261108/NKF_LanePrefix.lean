import NKF_LaneTrace
set_option autoImplicit false
noncomputable section
namespace NKF_LanePrefix
open Aeneas Aeneas.Std Result
abbrev Node := NKF_LaneTrace.Node
abbrev Frontier := NKF_LaneTrace.Frontier
/-- The chronological log is always a prefix, including the rejecting call.
No accepted-only hypothesis erases an error prefix. -/
theorem log_prefix {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) (levels : List (Fin 20))
 (before : Frontier) : ∃ suffix,
 levels=(NKF_LaneTrace.run empty occupied raw levels before).2.2++suffix := by
 induction levels generalizing before with
 | nil => exact ⟨[],rfl⟩
 | cons level rest ih =>
   cases stepEq : NKF_LaneTrace.iteration (empty level) (occupied level) before level (raw level) with
   | mk reply after =>
     cases reply with
     | Err e => exact ⟨rest,by simp only [NKF_LaneTrace.run,stepEq,List.cons_append,List.nil_append]⟩
     | Ok u =>
       obtain ⟨suffix,eq⟩:=ih after
       exact ⟨suffix,by simpa only [NKF_LaneTrace.run,stepEq,List.cons_append] using congrArg (List.cons level) eq⟩

theorem log_bound {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) (levels : List (Fin 20))
 (before : Frontier) :
 (NKF_LaneTrace.run empty occupied raw levels before).2.2.length≤levels.length := by
 obtain ⟨suffix,eq⟩:=log_prefix empty occupied raw levels before
 have lengths:=congrArg List.length eq
 simp only [List.length_append] at lengths
 omega

/-- Return-success forces the complete chronological list, not an arbitrary
subsequence. It does not claim the native loop has been certified. -/
theorem success_log {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) (levels : List (Fin 20))
 (before : Frontier)
 (accepted : (NKF_LaneTrace.run empty occupied raw levels before).1=.Ok ()) :
 (NKF_LaneTrace.run empty occupied raw levels before).2.2=levels := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
   cases stepEq : NKF_LaneTrace.iteration (empty level) (occupied level) before level (raw level) with
   | mk reply after =>
     cases reply with
     | Err e => simp only [NKF_LaneTrace.run,stepEq] at accepted;cases accepted
     | Ok u =>
       have h : (NKF_LaneTrace.run empty occupied raw rest after).1=.Ok () := by
         simpa only [NKF_LaneTrace.run,stepEq] using accepted
       simpa only [NKF_LaneTrace.run,stepEq] using congrArg (List.cons level) (ih after h)

#print axioms log_prefix
#print axioms log_bound
#print axioms success_log
end NKF_LanePrefix
