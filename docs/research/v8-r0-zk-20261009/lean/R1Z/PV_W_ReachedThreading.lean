import R1Z.PV_W_R_Entry
import R1Z.PV_W_Enriched
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_ReachedThreading
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading PV_W_Syntax
open PV_W_ReachedEffects PV_W_Callbacks
variable [ExternalTypes]
variable {W C : Type}

/-- Interpreter data at the reached types. Base helpers are unresolved
subprograms, not asserted pure. Reserve receives its actual allocator type,
and zeroize is restricted to the emitted primitive-byte dictionaries. -/
structure Algebra (W C : Type) where
  base : PV_W_TypedEffects.Algebra W C Aeneas.Std.Error
  reserve : {T : Type} → Type → alloc.vec.Vec T → Usize →
    M W C Aeneas.Std.Error ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)
  dropWords : alloc.vec.Vec U32 → M W C Aeneas.Std.Error Unit
  zeroArray : (N : Usize) → Array U8 N → M W C Aeneas.Std.Error (Array U8 N)
  zeroByte : U8 → M W C Aeneas.Std.Error U8

def interpret (a : Algebra W C) : Interpreter Op W C Aeneas.Std.Error
  | _, .base op => PV_W_TypedEffects.interpret a.base op
  | _, .reserve Allocator v n => a.reserve Allocator v n
  | _, .dropWords v => a.dropWords v
  | _, .zeroArray N v => a.zeroArray N v
  | _, .zeroByte v => a.zeroByte v

structure Laws (a : Algebra W C) (step : W → C → W → Prop) : Prop where
  base : ∀ {A : Type} (op : PV_W_TypedEffects.Primitive A),
    Valid step (PV_W_TypedEffects.interpret a.base op)
  reserve : ∀ {T : Type} (Allocator : Type) (v : alloc.vec.Vec T) n,
    Valid step (a.reserve Allocator v n)
  dropWords : ∀ v, Valid step (a.dropWords v)
  zeroArray : ∀ N v, Valid step (a.zeroArray N v)
  zeroByte : ∀ v, Valid step (a.zeroByte v)

theorem primitive_valid (a : Algebra W C) (step : W → C → W → Prop) (h : Laws a step)
    {A : Type} (op : Op A) : Valid step (interpret a op) := by
  cases op with
  | base op => exact h.base op
  | reserve Allocator v n => exact h.reserve Allocator v n
  | dropWords v => exact h.dropWords v
  | zeroArray N v => exact h.zeroArray N v
  | zeroByte v => exact h.zeroByte v

variable (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant) (hash : Hash)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)

/-- Exact recursive source result at the lifted hash. This does not assert
that arbitrary native callbacks are world-free. -/
theorem entry_source (ops : ExternalFuns) :
    erase ops (PV_W_R_Entry.program public1 compiled variant hash attempt store) =
      @prover.prove_masked_attempt _ ops public1 compiled variant (sourceHash ops hash) attempt store :=
  PV_W_R_Entry.erase_program ops public1 compiled variant hash attempt store

/-- Composition over the recursively spliced control flow. Local primitive,
remaining helper and lifetime/ownership adequacy are still P obligations. -/
theorem entry_threaded (a : Algebra W C) (step : W → C → W → Prop)
    (h : Laws a step) (w : W) :
    Threaded step w
      (eval (interpret a) (PV_W_R_Entry.program public1 compiled variant hash attempt store) w).calls
      (eval (interpret a) (PV_W_R_Entry.program public1 compiled variant hash attempt store) w).world :=
  eval_valid (interpret a) step (primitive_valid a step h) _ w

theorem entry_operational (a : Algebra W C) (w : W)
    (r : Run W C Aeneas.Std.Error
      ((core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) ×
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
    (h : PV_W_Syntax.Executes (interpret a)
      (PV_W_R_Entry.program public1 compiled variant hash attempt store) w r) :
    eval (interpret a) (PV_W_R_Entry.program public1 compiled variant hash attempt store) w = r :=
  execution_sound (interpret a) h

variable {Os Fs Allocator Extra Tag : Type}
/-- Projection of a full enriched run deletes only proven OS-silent steps.
No file-data or directory-durability assertion follows from this projection. -/
theorem project_run (a : Algebra (PV_W_Enriched.World Os Fs Allocator Extra) (Option Tag))
    (step : PV_W_Enriched.World Os Fs Allocator Extra → Option Tag →
      PV_W_Enriched.World Os Fs Allocator Extra → Prop)
    (osStep : Os → Tag → Os → Prop) (h : Laws a step)
    (silent : ∀ w n, step w none n → w.os=n.os)
    (visible : ∀ w n c, step w (some c) n → osStep w.os c n.os)
    (w : PV_W_Enriched.World Os Fs Allocator Extra) :
    Threaded osStep w.os
      (PV_W_Enriched.projectTrace PV_W_Enriched.World.os
        (eval (interpret a) (PV_W_R_Entry.program public1 compiled variant hash attempt store) w).calls)
      (eval (interpret a) (PV_W_R_Entry.program public1 compiled variant hash attempt store) w).world.os :=
  PV_W_Enriched.project_threaded PV_W_Enriched.World.os step osStep silent visible
    (entry_threaded public1 compiled variant hash attempt store a step h w)

#print axioms primitive_valid
#print axioms entry_source
#print axioms entry_threaded
#print axioms entry_operational
#print axioms project_run
end R1Z.PV_W_ReachedThreading
