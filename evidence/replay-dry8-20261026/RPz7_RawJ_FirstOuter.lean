import RPz7_RawJ_OuterHelpers
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_FirstOuter
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer RawJ_OuterBudget RawJ_OuterHelpers
attribute [local irreducible] S2W_Outer.first_decoded bounded

theorem first (sdk : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    bounded 1018 (stage1_owned sdk traceEffects program accounts data) := by
  unfold stage1_owned
  repeat' first
    | (solve | exact pure_bound _ _)
    | (solve | exact lift_bound _ _)
    | (solve | exact decoded sdk _ _ _ _)
    | (apply decoded_bind sdk; intro x)
    | (apply lift_bind;intro x)
    | (apply call_bind; (first | (solve | norm_num [cost]) | intro x))
    | (apply map_bind;intro x)
    | intro x
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [traceEffects])
    | split

#print axioms first
end AspisR1.RawJ_FirstOuter
end
