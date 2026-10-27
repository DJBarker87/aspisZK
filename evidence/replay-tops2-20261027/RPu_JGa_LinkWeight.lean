import RPu_JGa_LinkWeightSimple
import RPu_JGa_LinkWeightBits
import RPu_JGa_LinkBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_LinkWeight
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_copy_terminal

theorem source (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hg : JGa_LinkBounds.Good l) :
    ∃ w,link_weight l index v=ok w := by
  have kinds : l.weight_kind=0#u8 ∨ l.weight_kind=1#u8 ∨ l.weight_kind=2#u8 ∨ l.weight_kind=3#u8 ∨ l.weight_kind=4#u8 := by
    have h := hg.2.2.2.1
    rcases (by omega : l.weight_kind.val=0 ∨ l.weight_kind.val=1 ∨ l.weight_kind.val=2 ∨ l.weight_kind.val=3 ∨ l.weight_kind.val=4) with h|h|h|h|h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (Or.inl (UScalar.eq_of_val_eq h))
    · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (UScalar.eq_of_val_eq h))))
  rcases kinds with hk|hk|hk|hk|hk
  · obtain ⟨w,hw⟩ := JGa_LinkWeightSimple.zero l index v hk
    exact ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := JGa_LinkWeightSimple.transfer l index v hk
    exact ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := JGa_LinkWeightSimple.withdrawal l index v hk
    exact ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := JGa_LinkWeightBits.complement l index v hk hg.2.2.2.2
    exact ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := JGa_LinkWeightBits.keep l index v hk hg.2.2.2.2
    exact ⟨w,hw⟩
#print axioms source
end AspisR1.JGa_LinkWeight
end
