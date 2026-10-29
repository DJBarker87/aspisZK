import R1Z.PV_W_TypedReservation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_TypedThreading
open ProverRwFull PV_W_Syntax PV_W_Threading PV_W_TypedEffects PV_W_TypedReservation
open Aeneas.Std
variable [ExternalTypes]
variable {W C Err : Type}

/-- Local model-step obligations, not native source laws and not a new trust
item. Helpers must be interpreted recursively or discharged separately. -/
structure Laws (a : Algebra W C Err) (step : W → C → W → Prop) : Prop where
  helper : ∀ {A : Type} (op : PV_W_SourceSyntax.Op A), Valid step (a.helper op)
  fileOpen : ∀ {P : Type} (convert : ExternalFuns → core.convert.AsRef P std.path.Path) (path : P),
    Valid step (a.fileOpen convert path)
  fileSync : ∀ file, Valid step (a.fileSync file)
  optionsOpen : ∀ {P : Type} (convert : ExternalFuns → core.convert.AsRef P std.path.Path) options (path : P),
    Valid step (a.optionsOpen convert options path)
  errorKind : ∀ error, Valid step (a.errorKind error)
  writeAll : ∀ file bytes, Valid step (a.writeAll file bytes)

theorem primitive_valid (a : Algebra W C Err) (step : W → C → W → Prop)
    (laws : Laws a step) {A : Type} (op : Primitive A) : Valid step (interpret a op) := by
  cases op with
  | helper op => exact laws.helper op
  | fileOpen convert path => exact laws.fileOpen convert path
  | fileSync file => exact laws.fileSync file
  | optionsOpen convert options path => exact laws.optionsOpen convert options path
  | errorKind error => exact laws.errorKind error
  | writeAll file bytes => exact laws.writeAll file bytes

/-- Named composition over the typed frozen-source control flow. The local
laws above do not include the desired whole-caller statement. -/
theorem reservation_threads (a : Algebra W C Aeneas.Std.Error) (step : W → C → W → Prop)
    (laws : Laws a step)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) (w : W) :
    Threaded step w (eval (interpret a) (reserve self statement nonce) w).calls
      (eval (interpret a) (reserve self statement nonce) w).world :=
  eval_valid (interpret a) step (primitive_valid a step laws) _ w

theorem reservation_operational (a : Algebra W C Aeneas.Std.Error)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) (w : W)
    (r : Run W C Aeneas.Std.Error (Bool × aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
    (executed : Executes (interpret a) (reserve self statement nonce) w r) :
    eval (interpret a) (reserve self statement nonce) w = r :=
  execution_sound (interpret a) executed

theorem source_complete (dictionary : ExternalFuns)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Array U8 32#usize) :
    erase dictionary (reserve self statement nonce) =
      @aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
        _ dictionary self statement nonce :=
  erase_reserve dictionary self statement nonce

#print axioms primitive_valid
#print axioms reservation_threads
#print axioms reservation_operational
#print axioms source_complete
end R1Z.PV_W_TypedThreading
