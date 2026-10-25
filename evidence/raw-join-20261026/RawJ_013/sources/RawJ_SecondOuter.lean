import RawJ_OuterHelpers
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_SecondOuter
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer RawJ_OuterBudget RawJ_OuterHelpers
attribute [local irreducible] bounded S2W_Outer.mapError

theorem returned {A B : Type} (n : Nat) (a : A) (k : A → Code B)
    (h : bounded n (k a)) : bounded n ((monadLift (ok a) : Code A) >>= k) := h

theorem second (sdk : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) :
    bounded 903 (stage2_owned sdk traceEffects program accounts data slot) := by
  unfold stage2_owned
  simp only [AdapterRw.observer]
  repeat' first
    | (solve | exact pure_bound _ _)
    | (solve | exact lift_bound _ _)
    | (apply returned)
    | (apply lift_bind;intro x)
    | (apply call_bind; (first | (solve | norm_num [cost]) | intro x))
    | (apply map_bind;intro x)
    | intro x
    | (fail_if_no_progress dsimp only)
    | split

#print axioms returned
#print axioms second
end AspisR1.RawJ_SecondOuter
end
