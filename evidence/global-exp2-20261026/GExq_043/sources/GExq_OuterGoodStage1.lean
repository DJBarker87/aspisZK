import GExq_OuterGoodFirst
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodStage1
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace S2W_Outer
open GExq_OuterLower GExq_OuterGoodLaws

theorem stage1 (sdk : AdapterRw.Ops) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : S2Z.Oracle.NativeBinding sdk hashv)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) : Good hashv (stage1_owned sdk traceEffects program accounts data) := by
  unfold stage1_owned
  repeat' first
    | (solve | exact pure_good _ _)
    | (solve | exact lift_good _ _)
    | (solve | exact GExq_OuterGoodFirst.first_decoded sdk hashv law _ _ _ _)
    | (apply lift_bind_good;intro x)
    | (apply call_bind_good; (first | trivial | intro x))
    | (apply bind_good; (first | exact GExq_OuterGoodFirst.first_decoded sdk hashv law _ _ _ _ | intro x))
    | intro x
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [traceEffects])
    | split

#print axioms stage1
end AspisR1.GExq_OuterGoodStage1
end
