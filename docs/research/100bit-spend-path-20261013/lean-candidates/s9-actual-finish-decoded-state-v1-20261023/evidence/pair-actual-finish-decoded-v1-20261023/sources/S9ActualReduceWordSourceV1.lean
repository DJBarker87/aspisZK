import AspisR1S9ProductionPairCutV1.Funs
import CanonicalDotFinishSemantics
import S9CheckedWrappingSuccessV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualReduceWordSourceV1
open AspisR1S9CheckedWrappingSuccessV1
abbrev nativeReduce := AspisR1S9ProductionPairCutV1.fast_pairing.canonical.reduce
abbrev word := AspisR1CanonicalDotFinish.Proof.canonicalWord
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩
private theorem shift31 (r : U64) : r >>> 31#i32 = .ok (U64.wrapping_shr r 31#u32) := by rfl

/-- The current wrapping reducer returns the SAME canonical word as the
retained S5 checked reducer on every U64. Existing totality supplies successful
checked operations; no extra no-overflow/accepted-run premise is assumed. -/
theorem actual_reduce_word (x : U64) : nativeReduce x = .ok (word x) := by
  have h := AspisR1CanonicalDotFinish.Proof.canonical_reduce_total x
  unfold AspisR1CanonicalDotFinish.canonical.reduce at h
  simp only [AspisR1CanonicalDotFinish.canonical.P,lift,shift31,bind_tc_ok] at h
  obtain ⟨x1,h1,h⟩ := bind_success _ _ _ h
  obtain ⟨x2,h2,h⟩ := bind_success _ _ _ h
  have hw1 := u64_add_success _ _ _ h1
  have hw2 := u64_add_success _ _ _ h2
  unfold nativeReduce AspisR1S9ProductionPairCutV1.fast_pairing.canonical.reduce
  simp only [AspisR1S9ProductionPairCutV1.fast_pairing.canonical.P,lift,bind_tc_ok]
  rw [hw1,hw2]
  split at h
  · rename_i hge
    obtain ⟨x3,h3,h⟩ := bind_success _ _ _ h
    have hw3 := u64_sub_success _ _ _ h3
    rw [if_pos hge,hw3]
    exact h
  · rename_i hlt
    rw [if_neg hlt]
    exact h

#print axioms actual_reduce_word
end AspisR1S9ActualReduceWordSourceV1
