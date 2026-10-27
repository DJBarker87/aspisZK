import RPz7_GExq_OuterGoodMap
import RPz7_GExq_GoodTactic
import RPz7_GExq_OuterGoodBinds
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodStage2
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer
open GExq_OuterLower GExq_OuterGoodLaws

theorem returned_good {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (a : A) (k : A → Code B) (h : Good hashv (k a)) :
    Good hashv ((monadLift (ok a) : Code A) >>= k) := h

attribute [local irreducible] Good S2W_Outer.mapError

theorem stage2 (sdk : AdapterRw.Ops) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : S2Z.Oracle.NativeBinding sdk hashv)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    Good hashv (stage2_owned sdk traceEffects program accounts data slot) := by
  unfold stage2_owned
  simp only [AdapterRw.observer]
  repeat' first
    | (solve | exact pure_good _ _)
    | (solve | exact lift_good _ _)
    | (apply returned_good)
    | (apply lift_bind_good;intro x)
    | (apply call_bind_good)
    | (apply GExq_OuterGoodBinds.map_bind; intro x)
    | (solve | exact ⟨law,rfl⟩)
    | (solve | trivial)
    | intro x
    | (fail_if_no_progress dsimp only)
    | split

#print axioms returned_good
#print axioms stage2
end AspisR1.GExq_OuterGoodStage2
end
