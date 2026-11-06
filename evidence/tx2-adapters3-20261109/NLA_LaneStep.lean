import NLA_RootPrefix
set_option autoImplicit false
noncomputable section
namespace NLA_LaneStep
open Aeneas Aeneas.Std Result
open NKP_LaneCuts
/-- The root stage and every subsequent native iteration share the SAME
frontier oracle. This is a local composition theorem; no producer is assumed. -/
def run {F : Type} (root : Result (core.result.Result Node F))
 (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (levels : List (Fin 20)) (before : Frontier) :=
 NLA_RootPrefix.enter root (fun _ => ok (NKP_LaneInduction.fold step levels before))

theorem source_steps {F : Type} (root : Result (core.result.Result Node F))
 (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (cuts : ∀ before level, IterationCut (empty level) (occupied level) before
   (step before level).2 level (raw level) (step before level).1)
 (levels : List (Fin 20)) (before : Frontier) :
 run root empty occupied raw step levels before =
 NLA_RootPrefix.enter root (fun _ => ok (NKF_LaneTrace.run empty occupied raw levels before)) := by
 unfold run
 rw [NKP_LaneInduction.compose empty occupied raw step cuts levels before]

/-- A bad root executes no frontier step; changing every later oracle has
no effect on the error. This keeps the exact Result rather than success-only transport. -/
theorem bad_root {F : Type} (e : F)
 (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (levels : List (Fin 20)) (before : Frontier) :
 run (ok (.Err e)) empty occupied raw step levels before =
 ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := rfl

#print source_steps
#print axioms source_steps
#print axioms bad_root
end NLA_LaneStep
