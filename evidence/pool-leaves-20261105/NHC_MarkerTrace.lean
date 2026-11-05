import NHC_NGG_MarkerZero
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_MarkerTrace
/-- The observed bytes and the unconsumed suffix at the first nonzero byte.
This is a model loop law; native iterator/frame association is a separate gate. -/
def run : List U8 → Bool × List U8 × List U8
  | [] => (true, [], [])
  | b :: rest => if b.val = 0 then
      let r := run rest
      (r.1, b :: r.2.1, r.2.2)
    else (false, [b], rest)

theorem partition (bytes : List U8) : (run bytes).2.1 ++ (run bytes).2.2 = bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => by_cases h : b.val = 0 <;> simp [run, h, ih]
#print axioms partition

theorem value (bytes : List U8) : (run bytes).1 = (NHC_NGG_MarkerZero.scan bytes).1 := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => by_cases h : b.val = 0 <;> simp [run, NHC_NGG_MarkerZero.scan, h, ih]
#print axioms value

theorem count (bytes : List U8) : (run bytes).2.1.length = (NHC_NGG_MarkerZero.scan bytes).2 := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => by_cases h : b.val = 0 <;> simp [run, NHC_NGG_MarkerZero.scan, h, ih]
#print axioms count

theorem zero_prefix (pre tail : List U8) (zeros : ∀ b ∈ pre, b.val = 0) :
    run (pre ++ tail) = ((run tail).1, pre ++ (run tail).2.1, (run tail).2.2) := by
  induction pre with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.val = 0 := zeros b (by simp)
    have hs : ∀ x ∈ bs, x.val = 0 := by intro x hx; exact zeros x (by simp [hx])
    simp [run, hb, ih hs]
#print axioms zero_prefix

theorem reject_frame (pre suffix : List U8) (bad : U8)
    (zeros : ∀ b ∈ pre, b.val = 0) (nonzero : bad.val ≠ 0) :
    run (pre ++ bad :: suffix) = (false, pre ++ [bad], suffix) := by
  rw [zero_prefix pre (bad :: suffix) zeros]
  simp [run, nonzero]
#print axioms reject_frame

theorem accepted (bytes : List U8) (zeros : ∀ b ∈ bytes, b.val = 0) :
    run bytes = (true, bytes, []) := by
  simpa [run] using zero_prefix bytes [] zeros
#print axioms accepted
end NHC_MarkerTrace
