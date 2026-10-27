import JGa_LinkBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_LinkWeight
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_copy_terminal

@[step] theorem equal (v w : PoolV1PairForestCompiledVariantV1) :
    PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq v w ⦃ _ => True ⦄ := by
  unfold PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
  trivial
#print axioms equal

@[step] theorem source (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hg : JGa_LinkBounds.Good l) :
    link_weight l index v ⦃ out => out.val<2147483647 ⦄ := by
  have kinds : l.weight_kind=0#u8 ∨ l.weight_kind=1#u8 ∨ l.weight_kind=2#u8 ∨ l.weight_kind=3#u8 ∨ l.weight_kind=4#u8 := by
    have h := hg.2.2.2.1
    rcases (by omega : l.weight_kind.val=0 ∨ l.weight_kind.val=1 ∨ l.weight_kind.val=2 ∨ l.weight_kind.val=3 ∨ l.weight_kind.val=4) with h|h|h|h|h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (Or.inl (UScalar.eq_of_val_eq h))
    · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq h))))
  rcases kinds with hk|hk|hk|hk|hk
  all_goals unfold link_weight
  all_goals rw [hk]
  all_goals step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_LinkWeight
end
