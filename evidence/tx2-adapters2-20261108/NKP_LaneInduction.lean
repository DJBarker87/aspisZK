import NKP_LaneCuts
set_option autoImplicit false
noncomputable section
namespace NKP_LaneInduction
open Aeneas Aeneas.Std Result
open NKP_LaneCuts
/-- Local native iteration fold. Each step is constrained by its field/result
cut on every arbitrary pre-state; no whole-loop equality is an input. -/
def fold (step : Frontier → Fin 20 → Reply × Frontier) :
 List (Fin 20) → Frontier → Reply × Frontier × List (Fin 20)
 | [],before => (.Ok (),before,[])
 | level::rest,before =>
   let (reply,after) := step before level
   match reply with
   | .Err e => (.Err e,after,[level])
   | .Ok _ =>
     let (result,final,calls) := fold step rest after
     (result,final,level::calls)

theorem compose {F : Type} (empty : Fin 20 → Node)
 (occupied : Fin 20 → Bool) (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (cuts : ∀ before level, IterationCut (empty level) (occupied level) before
   (step before level).2 level (raw level) (step before level).1)
 (levels : List (Fin 20)) (before : Frontier) :
 fold step levels before = NKF_LaneTrace.run empty occupied raw levels before := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
   have same := NKP_LaneCuts.iteration (empty level) (occupied level) before
     (step before level).2 level (raw level) (step before level).1 (cuts before level)
   have step_eq : step before level = NKF_LaneTrace.iteration
       (empty level) (occupied level) before level (raw level) := by
     simpa only [Prod.mk.eta] using same
   simp only [fold,NKF_LaneTrace.run,step_eq]
   cases h : NKF_LaneTrace.iteration (empty level) (occupied level) before level (raw level) with
   | mk reply after =>
     simp only [h]
     cases reply with
     | Err e => rfl
     | Ok u => rw [ih after]

/-- Error/abort prefixes keep every already-entered call and omit the suffix;
there is no accepted-only restriction. This is model composition support,
not yet association of the full frozen lane body with op50. -/
theorem chronological {F : Type} (empty : Fin 20 → Node)
 (occupied : Fin 20 → Bool) (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (cuts : ∀ before level, IterationCut (empty level) (occupied level) before
   (step before level).2 level (raw level) (step before level).1)
 (levels : List (Fin 20)) (before : Frontier) :
 ∃ suffix, levels = (fold step levels before).2.2 ++ suffix := by
 rw [compose empty occupied raw step cuts levels before]
 exact NKF_LanePrefix.log_prefix empty occupied raw levels before

#print axioms compose
#print axioms chronological
end NKP_LaneInduction
