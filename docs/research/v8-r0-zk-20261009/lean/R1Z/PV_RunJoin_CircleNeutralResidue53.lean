import R1Z.PV_RunJoin_CircleNeutralReduce53
import AspisV8R19.PartialProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralResidue53
open PV_RunJoin_CircleNeutralFold53 PV_RunJoin_CircleNeutralReduce53

theorem fold_mod (x : U64) : (fold x).val % 2147483647 = x.val % 2147483647 := by
  rw [fold_val]
  exact AspisV8R19.PartialProduct.partial_mod x.val

theorem subtract_mod (x : U32) (hx : x.val<4294967294) :
    (PV_RunJoin_CircleNeutralSubtract53.output x).val % 2147483647 = x.val % 2147483647 := by
  rw [PV_RunJoin_CircleNeutralSubtract53.value]
  split <;> omega

theorem reduce_mod (x : U64) : ∃ y,
    PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x = ok y ∧
      y.val = x.val % 2147483647 := by
  obtain ⟨y,hy,hc⟩ := total x
  refine ⟨y,hy,?_⟩
  have he : y = PV_RunJoin_CircleNeutralSubtract53.output (word x) := by
    have h := (source x).trans (PV_RunJoin_CircleNeutralSubtract53.source (word x))
    exact Result.ok.inj (hy.symm.trans h)
  have hm := subtract_mod (word x) (by rw [word_val];exact fold_twice_bound x)
  rw [← he,word_val,fold_mod,fold_mod] at hm
  rw [Nat.mod_eq_of_lt hc] at hm
  exact hm

#print axioms fold_mod
#print axioms subtract_mod
#print axioms reduce_mod
end R1Z.PV_RunJoin_CircleNeutralResidue53
