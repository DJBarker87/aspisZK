import S9HighTermSourceCellRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9HighTermPolynomialMeaningRootV1
open AspisR1S9HelperP6
open S2LibraFactoredIdentity
theorem actual_term_is_scaled_power
    (ap1 : Array W (4#usize)) (high : Array Q (4#usize))
    (seed : Q) (i : Usize) (hi : i.val < 4)
    (call : AspisR1S9HighTermsConcreteV1.HighTermCall ap1 high i)
    (hhigh : ∀ j z, Array.index_usize high j = .ok z →
      DQ z = DQ seed ^ (4*j.val)) :
    D call.term = scaled (fun j => D (cell ap1 j))
      (AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER)
      ⟨i.val,hi⟩ *
      (algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM
        AspisWideTower.WideExact (DQ seed)) ^ (4*i.val) := by
  have hx := actual_term_source_cell ap1 high i hi call
  have hq := hhigh i call.q call.high_read
  have hd := call.term_decode_generated
  dsimp only [D, DQ, AspisR1S9HighTermsTraceV1.decW,
    AspisR1S9HighTermsTraceV1.decQ] at hq ⊢
  rw [hd, hq, ← hx, map_pow]
  unfold scaled
  ring

#print axioms actual_term_is_scaled_power
end AspisR1.S9HighTermPolynomialMeaningRootV1
