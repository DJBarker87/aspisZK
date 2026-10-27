import RPt_RPx_OuterDecoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_OuterStage1
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace S2W_Outer RPx_OuterCredit
attribute [local irreducible] Credit S2W_Outer.first_decoded

theorem stage1 (sdk : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) : Credit (stage1_owned sdk traceEffects program accounts data) 1018 := by
  unfold stage1_owned
  repeat' first
    | (solve | exact pure_credit _ _)
    | (solve | exact lift_credit _ _)
    | (solve | exact RPx_OuterDecoded.first_decoded sdk _ _ _ _)
    | (apply lift_bind_credit;intro x)
    | (apply call_bind_credit; (first | (solve | simp only [charge];omega) | intro x))
    | (apply RPx_OuterDecoded.first_bind sdk;intro x)
    | intro x
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [traceEffects])
    | split

#print axioms stage1
end AspisR1.RPx_OuterStage1
end
