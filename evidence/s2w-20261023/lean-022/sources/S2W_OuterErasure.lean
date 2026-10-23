import S2W_Outer
set_option autoImplicit false
namespace AspisR1.S2W_OuterErasure
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace S2W_Outer

theorem erase_pure (ops : Ops) {A : Type} (a : A) :
    erase ops (pure a) = ok a := rfl

theorem erase_liftM (ops : Ops) {A : Type} (r : Result A) :
    erase ops (monadLift r : Code A) = r := erase_lift ops r

theorem erase_if (ops : Ops) {A : Type} (p : Prop) [Decidable p]
    (yes no : Code A) : erase ops (if p then yes else no) =
      if p then erase ops yes else erase ops no := by split <;> rfl

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) :=
  congrArg (fun k => r >>= k) (funext h)

theorem erase_mapError (ops : Ops) {A : Type}
    (r : core.result.Result A aspis_r1_cost_probe.verifier.Error) :
    erase ops (mapError traceEffects.op44 r) =
      AdapterRw.core.result.Result.map_err
        (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error solana_program_error.ProgramError)
        r ops.op44 := by cases r <;> rfl

theorem first_erasure (ops : Ops)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) :
    erase ops (S2W_Outer.first_decoded ops traceEffects public1 public_bytes proof k) =
      AdapterRw.first_decoded ops public1 public_bytes proof k := by
  simp only [S2W_Outer.first_decoded, AdapterRw.first_decoded, erase_bind,
    erase_liftM, erase_mapError, traceEffects, erase_perform, invoke]

-- Congruence follows each actual branch. No accepted-run cut is a premise.
theorem stage1_erasure (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    erase ops (stage1_owned ops traceEffects program_id accounts data) =
      r1_pool_adapter.owned.stage1_owned ops program_id accounts data := by
  simp only [stage1_owned, r1_pool_adapter.owned.stage1_owned, traceEffects,
    erase_bind, erase_liftM, erase_pure, erase_perform, invoke, erase_if, first_erasure, erase_mapError]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind, erase_liftM,
        erase_pure, erase_perform, invoke, erase_if, first_erasure, erase_mapError])
    | (apply bind_congr; intro x)
    | split

theorem stage2_erasure (ops : Ops) (program_id : solana_pubkey.Pubkey)
    (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
    (slot : core.result.Result U64 solana_program_error.ProgramError) :
    erase ops (stage2_owned ops traceEffects program_id accounts data slot) =
      r1_pool_adapter.owned.stage2_owned ops program_id accounts data slot := by
  simp only [stage2_owned, r1_pool_adapter.owned.stage2_owned, traceEffects,
    erase_bind, erase_liftM, erase_pure, erase_perform, invoke, erase_if, first_erasure, erase_mapError]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind, erase_liftM,
        erase_pure, erase_perform, invoke, erase_if, first_erasure, erase_mapError])
    | (apply bind_congr; intro x)
    | split

#print axioms erase_mapError
#print axioms first_erasure
#print axioms erase_pure
#print axioms erase_liftM
#print axioms erase_if
#print axioms stage1_erasure
#print axioms stage2_erasure
end AspisR1.S2W_OuterErasure
