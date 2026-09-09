import CopyTagSplit
namespace AspisV8.CopyTagShared
open AspisV8.CopyTagSplit

-- The shared field sum is canonical, not the old unreduced integer sum.
theorem reduced_sum_mod (b s d modulus : Nat) :
    (b*s+d)%modulus = (b*(s%modulus)+d)%modulus := by
  rw [Nat.add_mod, Nat.add_mod (b*(s%modulus))]
  congr 1
  rw [Nat.mul_mod b s, Nat.mul_mod b (s%modulus), Nat.mod_mod]

theorem shared_accumulator_mod (xs : List (Nat × Nat)) :
    (xs.map (fun x => x.1*(base+x.2))).sum % p =
      (67*rotated ((xs.map Prod.fst).sum%p) + (xs.map (fun x => x.1*x.2)).sum)%p := by
  rw [list_split,reduced_sum_mod,split_mod]

theorem shared_final_bound (s d : Nat) (hs : s < p)
    (hd : d ≤ 78855599481120) :
    67*rotated s+d < 2^64 ∧ (67*rotated s+d)%(2^64)=67*rotated s+d := by
  have hb : s ≤ 584115551712 := by dsimp [p] at hs; omega
  exact ⟨(final_raw_bound s d hb hd).2,wrapping_final_exact s d hb hd⟩

theorem shared_loop_endpoint (xs : List (Nat × Nat))
    (hn : xs.length ≤ 272) (ha : ∀ x ∈ xs, x.1 < p)
    (hi : ∀ x ∈ xs, x.2 ≤ 135) :
    let raw := 67*rotated ((xs.map Prod.fst).sum%p)+(xs.map (fun x => x.1*x.2)).sum
    raw<2^64 ∧ raw%p=(xs.map (fun x => x.1*(base+x.2))).sum%p := by
  dsimp
  have hd := (accumulators_bound xs hn ha hi).2
  have hs : (xs.map Prod.fst).sum%p<p := Nat.mod_lt _ (by norm_num [p])
  exact ⟨(shared_final_bound _ _ hs hd).1,(shared_accumulator_mod xs).symm⟩

#print axioms reduced_sum_mod
#print axioms shared_accumulator_mod
#print axioms shared_final_bound
#print axioms shared_loop_endpoint
end AspisV8.CopyTagShared
