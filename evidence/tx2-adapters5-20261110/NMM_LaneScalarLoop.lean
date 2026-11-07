import NMM_LaneReplies
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NMM_LaneScalarLoop
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
attribute [local instance] Classical.propDecidable

def one {F : Type} (empty : Node) (occupied : Bool) (before : U32)
 (level selected : Fin 20) (word : Fin 8) (raw : core.result.Result Node F) : Reply × U32 :=
 match raw with
 | .Err _ => (.Err .InvalidAccountData,before)
 | .Ok node => (NKF_LaneFactor.guard empty node occupied,
   if selected=level then node word else before)

theorem one_projection {F : Type} (empty : Node) (occupied : Bool)
 (before : Frontier) (level selected : Fin 20) (word : Fin 8)
 (raw : core.result.Result Node F) :
 ((NKF_LaneTrace.iteration empty occupied before level raw).1,
  (NKF_LaneTrace.iteration empty occupied before level raw).2 selected word) =
 one empty occupied (before selected word) level selected word raw := by
 cases raw with
 | Err e => rfl
 | Ok node =>
  rw [NKF_LaneFactor.success_step]
  simp only [one,NJD_LaneStep.write,ite_apply]

def run {F : Type} (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F) (selected : Fin 20) (word : Fin 8) :
 List (Fin 20) → U32 → Reply × U32 × List (Fin 20)
 | [],before => (.Ok (),before,[])
 | level::rest,before =>
  let current := one (empty level) (occupied level) before level selected word (raw level)
  match current.1 with
  | .Err e => (.Err e,current.2,[level])
  | .Ok _ =>
   let tail := run empty occupied raw selected word rest current.2
   (tail.1,tail.2.1,level::tail.2.2)

def observe (selected : Fin 20) (word : Fin 8)
 (out : Reply × Frontier × List (Fin 20)) : Reply × U32 × List (Fin 20) :=
 (out.1,out.2.1 selected word,out.2.2)

/-- The selected-word state is sufficient for the complete returning loop
Result and exact call prefix. Rejected post-write state is retained locally;
no post-abort heap observation is asserted. -/
theorem loop_projection {F : Type} (empty : Fin 20 → Node)
 (occupied : Fin 20 → Bool) (raw : Fin 20 → core.result.Result Node F)
 (selected : Fin 20) (word : Fin 8) (levels : List (Fin 20)) (before : Frontier) :
 observe selected word (NKF_LaneTrace.run empty occupied raw levels before) =
 run empty occupied raw selected word levels (before selected word) := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
  simp only [NKF_LaneTrace.run,run]
  rw [←one_projection (empty level) (occupied level) before level selected word (raw level)]
  cases h : NKF_LaneTrace.iteration (empty level) (occupied level) before level (raw level) with
  | mk reply after =>
   simp only [h]
   cases reply with
   | Err e => rfl
   | Ok u => rw [←ih after];rfl

#print one_projection
#print axioms one_projection
#print loop_projection
#print axioms loop_projection
end NMM_LaneScalarLoop
