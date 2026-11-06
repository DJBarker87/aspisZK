import NLA_AllocationPrefix
set_option autoImplicit false
noncomputable section
namespace NLA_LaneAssemble
open Aeneas Aeneas.Std Result
open NKP_LaneCuts
abbrev Lane := NKP_LaneCompletion.Lane
abbrev PE := NKP_LaneCompletion.PE
/-- Source-ordered post-header composition, including the actual root in the
terminal zero-root guard and the allocation partiality. Local cut algebra;
no claim that a native whole invocation has produced this chain. -/
def complete {F : Type} (rootReply : Result (core.result.Result Node F))
 (loop : Reply × Frontier × List (Fin 20)) (action : Result Unit)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (emptyRoot : Node) : Result (core.result.Result Lane PE) := do
 let rootResult ← rootReply
 match rootResult with
 | .Err _ => ok (.Err .InvalidAccountData)
 | .Ok root =>
   NLA_AllocationPrefix.allocate action
    (NKP_LaneCompletion.finish bump master lane next root emptyRoot loop).1

theorem source_steps {F : Type}
 (rootReply : Result (core.result.Result Node F))
 (empty : Fin 20 → Node) (occupied : Fin 20 → Bool)
 (raw : Fin 20 → core.result.Result Node F)
 (step : Frontier → Fin 20 → Reply × Frontier)
 (cuts : ∀ before level, IterationCut (empty level) (occupied level) before
   (step before level).2 level (raw level) (step before level).1)
 (levels : List (Fin 20)) (before : Frontier) (action : Result Unit)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (emptyRoot : Node) :
 complete rootReply (NKP_LaneInduction.fold step levels before) action bump master lane next emptyRoot =
 complete rootReply (NKF_LaneTrace.run empty occupied raw levels before) action bump master lane next emptyRoot := by
 rw [NKP_LaneInduction.compose empty occupied raw step cuts levels before]

theorem root_error {F : Type} (e : F)
 (loop : Reply × Frontier × List (Fin 20)) (action : Result Unit)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (emptyRoot : Node) :
 complete (ok (.Err e)) loop action bump master lane next emptyRoot =
 ok (.Err .InvalidAccountData) := rfl

theorem loop_error {F : Type} (root : Node) (e : PE)
 (state : Frontier) (calls : List (Fin 20)) (action : Result Unit)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (emptyRoot : Node) :
 @complete F (ok (.Ok root)) (.Err e,state,calls) action bump master lane next emptyRoot =
 ok (.Err e) := rfl

/-- A loop error does not enter Box::new even if allocation would abort. -/
theorem error_ignores_allocator {F : Type} (root : Node) (e : PE)
 (state : Frontier) (calls : List (Fin 20)) (action₁ action₂ : Result Unit)
 (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (emptyRoot : Node) :
 @complete F (ok (.Ok root)) (.Err e,state,calls) action₁ bump master lane next emptyRoot =
 @complete F (ok (.Ok root)) (.Err e,state,calls) action₂ bump master lane next emptyRoot := rfl

#print source_steps
#print axioms source_steps
#print axioms root_error
#print axioms loop_error
#print axioms error_ignores_allocator
end NLA_LaneAssemble
