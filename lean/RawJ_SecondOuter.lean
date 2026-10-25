import RawJ_OuterHelpers
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_SecondOuter
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer RawJ_OuterBudget RawJ_OuterHelpers

theorem returned {A B : Type} (n : Nat) (a : A) (k : A → Code B)
    (h : bounded n (k a)) : bounded n ((monadLift (ok a) : Code A) >>= k) := h

theorem call_bound {A : Type} (n : Nat) (op : Call A) (le : cost op ≤ n) :
    bounded n (perform op) := ⟨le,fun _ => trivial⟩

#print axioms call_bound
attribute [local irreducible] bounded S2W_Outer.mapError

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
    | (apply RawJ_OuterHelpers.map_bind;intro x)
    | (solve | apply call_bound; norm_num [cost])
    | intro x
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [cost,Nat.sub_zero,Nat.sub_self,traceEffects])
    | split

#print axioms returned
#print axioms second
end AspisR1.RawJ_SecondOuter
end
