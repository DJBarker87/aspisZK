import AspisR1RecordParser.Funs

/-! The actual generated high-component getter and derived comparison.
No canonicality or loop invariant is assumed. -/
set_option autoImplicit false

namespace AspisR1.ExtractedRecordHighZero
open Aeneas Aeneas.Std Result
open AspisR1RecordParser.field

theorem qm31_ne_false_iff (x y : QM31) :
    core.cmp.PartialEq.ne.trait_default QM31.Insts.CoreCmpPartialEqQM31 x y =
      ok false ↔ x = y := by
  rcases x with ⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩
  rcases y with ⟨⟨b0, b1⟩, ⟨b2, b3⟩⟩
  simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    QM31.Insts.CoreCmpPartialEqQM31, QM31.Insts.CoreCmpPartialEqQM31.eq,
    CM31.Insts.CoreCmpPartialEqCM31.eq, M31.Insts.CoreCmpPartialEqM31.eq,
    bind_tc_ok]
  by_cases h0 : a0 = b0
  · by_cases h1 : a1 = b1
    · by_cases h2 : a2 = b2
      · by_cases h3 : a3 = b3
        · simp [h0, h1, h2, h3]
        · simp [h0, h1, h2, h3]
      · simp [h0, h1, h2]
    · simp [h0, h1]
  · simp [h0]

theorem high_guard_false_iff (w : wide_exact.WideExact) :
    (do
      let q ← wide_exact.WideExact.impl.c1 w
      core.cmp.PartialEq.ne.trait_default QM31.Insts.CoreCmpPartialEqQM31 q QM31.ZERO) =
        ok false ↔ w.c1 = QM31.ZERO := by
  simp only [wide_exact.WideExact.impl.c1, bind_tc_ok, qm31_ne_false_iff]

theorem qm31_eq_zero_iff (q : QM31) :
    q = QM31.ZERO ↔
      q.c0.a = 0#u32 ∧ q.c0.b = 0#u32 ∧ q.c1.a = 0#u32 ∧ q.c1.b = 0#u32 := by
  rcases q with ⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩
  simp [QM31.ZERO, and_assoc]

end AspisR1.ExtractedRecordHighZero

#print axioms AspisR1.ExtractedRecordHighZero.qm31_ne_false_iff
#print axioms AspisR1.ExtractedRecordHighZero.high_guard_false_iff
#print axioms AspisR1.ExtractedRecordHighZero.qm31_eq_zero_iff
