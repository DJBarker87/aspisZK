import RPx_OuterCredit
import GExq_OuterGoodBinds
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_OuterDecoded
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace S2W_Outer RPx_OuterCredit

theorem map_credit {A : Type}
    (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    Credit (mapError traceEffects.op44 r) 0 := by
  cases r with
  | Ok a => exact pure_credit _ _
  | Err e =>
    apply call_bind_credit
    · exact Nat.le_refl 0
    · intro out;exact pure_credit _ _

theorem map_bind {A B : Type}
    (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error)
    (k : core.result.Result A AdapterRw.solana_program_error.ProgramError → Code B) (n : Nat)
    (hk : ∀ r,Credit (k r) n) : Credit (mapError traceEffects.op44 r >>= k) n := by
  simpa only [Nat.zero_add] using bind_credit _ _ 0 n (map_credit r) hk

theorem first_decoded (sdk : AdapterRw.Ops)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    Credit (S2W_Outer.first_decoded sdk traceEffects semantic pub proof split) 1018 := by
  unfold S2W_Outer.first_decoded
  change Credit (perform (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
    semantic pub proof split () none) >>= fun r => mapError (fun e=>perform (.op44 e)) r) 1018
  apply call_bind_credit
  · exact Nat.le_refl 1018
  · intro r;exact map_credit r

theorem first_bind {A : Type} (sdk : AdapterRw.Ops)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (k : core.result.Result (alloc.vec.Vec U8) AdapterRw.solana_program_error.ProgramError → Code A)
    (hk : ∀ r,Credit (k r) 0) :
    Credit (S2W_Outer.first_decoded sdk traceEffects semantic pub proof split >>= k) 1018 := by
  simpa only [Nat.add_zero] using bind_credit _ _ 1018 0 (first_decoded sdk semantic pub proof split) hk

#print axioms map_credit
#print axioms map_bind
#print axioms first_decoded
#print axioms first_bind
end AspisR1.RPx_OuterDecoded
end
