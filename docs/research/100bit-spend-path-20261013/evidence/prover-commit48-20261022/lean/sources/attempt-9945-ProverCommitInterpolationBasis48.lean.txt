import R1Z.ProverCommitM31Array48
import R1Z.ProverCommitBasisCounter47
/-! Exact descending interpolation basis update; all still-needed lower
coefficients are preserved. No 28-step array term is normalized. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInterpolationBasis48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitM31Ops48 ProverCommitM31Array48

def coefficient (xs : Nat → U32) (j : U32) (k : Nat) : M :=
  (if k=0 then 0 else decode (xs (k-1)))-decode (xs k)*decode j

attribute [local irreducible] array coefficient

theorem basis_value (xs : Nat → U32) (hxs : ∀ k, k < 28 → canonical (xs k))
    (j : U32) (n : Nat) (left : U8) (hleft : left.val=n) (bound : n ≤ 28) :
    ∃ ys : Nat → U32, basis_mul (array 28#usize xs) j left=ok (array 28#usize ys) ∧
      (∀ k, k < 28 → canonical (ys k)) ∧
      ∀ k, k < 28 → decode (ys k)=if k < n then coefficient xs j k else decode (xs k) := by
  induction n generalizing xs left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [basis_mul,hz];rfl
    · intro k hk;rw [if_neg (by omega)]
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    let kidx := UScalar.cast .Usize (U8.wrapping_sub left 1#u8)
    have hidx : kidx.val=n := by scalar_tac
    have hk : kidx.val < (28#usize).val := by change kidx.val < 28;rw [hidx];omega
    let shifted := if n=0 then 0#u32 else xs (n-1)
    have hcshift : canonical shifted := by
      by_cases hz : n=0
      · simp only [shifted,hz,if_true];decide
      · simpa only [shifted,hz,if_false] using hxs (n-1) (by omega)
    obtain ⟨product,hprod,hcprod,hdprod⟩ := mul_exact (xs n) j
    obtain ⟨z,hz,hcz,hdz⟩ := sub_exact shifted product hcshift hcprod
    let next := Function.update xs n z
    have hcnext : ∀ k, k < 28 → canonical (next k) := by
      intro k hk1
      by_cases he : k=n
      · subst k;simpa only [next,Function.update_self] using hcz
      · simpa only [next,Function.update_of_ne he] using hxs k hk1
    obtain ⟨ys,hy,hcy,hval⟩ := ih next hcnext _ hdec (by omega)
    have hshift : decode shifted=(if n=0 then 0 else decode (xs (n-1))) := by
      have zdecode : decode (0#u32)=0 := rfl
      by_cases he : n=0 <;> simp only [shifted,he,if_true,if_false,zdecode]
    have hvalue : decode z=coefficient xs j n := by
      rw [hdz,hshift,hdprod,coefficient]
    refine ⟨ys,?_,hcy,?_⟩
    · rw [basis_mul]
      simp only [hn,if_false,lift,bind_tc_ok]
      rw [predecessor_value xs kidx hk]
      simp only [bind_tc_ok,hidx]
      rw [index 28#usize xs kidx hk]
      simp only [hidx,hprod,bind_tc_ok]
      change (do let value ← field.M31.sub shifted product
                 let basis ← Aeneas.Std.Array.update (array 28#usize xs) kidx value
                 basis_mul basis j (U8.wrapping_sub left 1#u8))=ok (array 28#usize ys)
      rw [hz]
      simp only [bind_tc_ok]
      rw [update 28#usize xs kidx hk]
      simp only [hidx,bind_tc_ok]
      exact hy
    · intro k hk1
      rw [hval k hk1]
      by_cases he : k=n
      · rw [if_neg (by omega),if_pos (by omega)]
        simpa only [next,he,Function.update_self] using hvalue
      · by_cases ht : k < n
        · rw [if_pos ht,if_pos (by omega)]
          have hp : k-1≠n := by omega
          simp only [coefficient,next,Function.update_of_ne he,Function.update_of_ne hp]
        · rw [if_neg ht,if_neg (by omega)]
          simp only [next,Function.update_of_ne he]

#print axioms basis_value
end R1Z.ProverCommitInterpolationBasis48
