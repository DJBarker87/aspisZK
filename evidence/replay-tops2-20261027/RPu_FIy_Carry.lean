import RPu_FIq_Native08
import RPu_FIy_FrontierBits
import RPu_FIw_WordValue
import R0P.Digest
set_option autoImplicit false
namespace AspisR1.FIy_Carry
open Aeneas Aeneas.Std Result FIq_Native
abbrev loop := pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop

theorem low (index : U64) : (index &&& 1#u64)=0#u64 ↔ (index.val &&& 1)=0 := by
  constructor
  · intro h
    have v := congrArg UScalar.val h
    rw [UScalar.val_and] at v
    exact v
  · intro h
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    exact h

theorem value (fuel : Nat) (index : U64) (carry out : Usize)
    (span : carry.val+fuel=20) (success : loop index carry=ok out) :
    out.val=carry.val+R0P.digestTrailingOnes fuel index.val := by
  induction fuel generalizing index carry with
  | zero=>
    rw [loop,pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
      if_neg (show ¬carry<20#usize by change ¬carry.val<20;omega)] at success
    cases Result.ok.inj success
    rfl
  | succ fuel ih=>
    rw [loop,pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop.eq_def,
      if_pos (show carry<20#usize by change carry.val<20;omega)] at success
    simp only [lift,bind_tc_ok] at success
    split at success
    next hz=>
      cases Result.ok.inj success
      simp only [R0P.digestTrailingOnes,if_pos ((low index).mp hz),Nat.add_zero]
    next hz=>
      obtain ⟨index1,hi,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨carry1,hc,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨index2,hshift,hspec⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec index 1#u32 (by decide))
      have eq := Result.ok.inj (hshift.symm.trans hi)
      subst index2
      have shiftValue : index1.val=index.val >>> 1 := by
        have v := congrArg BitVec.toNat hspec.2
        exact v
      have carryValue := FIw_WordValue.add carry 1#usize carry1 hc
      change carry1.val=carry.val+1 at carryValue
      have rest := ih index1 carry1 (by omega) success
      have nzero : ¬(index.val &&& 1)=0 := fun h=>hz ((low index).mpr h)
      rw [rest,carryValue,shiftValue]
      simp only [R0P.digestTrailingOnes,if_neg nzero]
      omega

theorem caller (index : U64) (out : Usize)
    (success : pool_v1.pair_forest_semantic_terminal.bounded_append_carry index=ok out) :
    out.val=R0P.digestCarry index.val ∧ out.val≤20 := by
  have v := value 20 index 0#usize out (by rfl) success
  change out.val=0+R0P.digestCarry index.val at v
  rw [Nat.zero_add] at v
  exact ⟨v,v ▸ R0P.digest_carry_le index.val⟩
#print axioms low
#print axioms value
#print axioms caller
end AspisR1.FIy_Carry
