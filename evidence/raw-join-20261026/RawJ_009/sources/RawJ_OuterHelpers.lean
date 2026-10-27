import RawJ_OuterBudget
import GExq_OuterGoodBinds
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_OuterHelpers
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer RawJ_OuterBudget

theorem map_bound {A : Type} (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    bounded 0 (mapError traceEffects.op44 r) := by
  cases r with
  | Ok a => exact pure_bound _ _
  | Err e =>
    apply call_bind
    · exact Nat.le_refl _
    · intro error; exact pure_bound _ _

theorem map_bind {A B : Type} (n : Nat)
    (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error)
    (k : core.result.Result A AdapterRw.solana_program_error.ProgramError → Code B)
    (hk : ∀ a, bounded n (k a)) : bounded n (mapError traceEffects.op44 r >>= k) := by
  have h := bind_bound _ k 0 n (map_bound r) hk
  simpa only [Nat.zero_add] using h

theorem decoded (sdk : AdapterRw.Ops)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    bounded 1018 (first_decoded sdk traceEffects semantic pub proof split) := by
  unfold first_decoded
  change bounded 1018 (perform (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
    semantic pub proof split () none) >>= fun r => mapError (fun e => perform (.op44 e)) r)
  apply call_bind
  · exact Nat.le_refl _
  · intro r
    exact map_bound r

theorem decoded_bind {A : Type} (sdk : AdapterRw.Ops)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (k : core.result.Result (alloc.vec.Vec U8) AdapterRw.solana_program_error.ProgramError → Code A)
    (hk : ∀ r, bounded 0 (k r)) :
    bounded 1018 (first_decoded sdk traceEffects semantic pub proof split >>= k) := by
  exact bind_bound _ _ 1018 0 (decoded sdk semantic pub proof split) hk

#print axioms map_bound
#print axioms map_bind
#print axioms decoded
#print axioms decoded_bind
end AspisR1.RawJ_OuterHelpers
end
