import S3VariantRowPrefixFormula
import S3S9CurrentSourceModel

namespace AspisR1.S3VariantRowAeneasCut

theorem rowPrefix_eq_current_s2Row (j : Nat) :
    rowPrefix j 5 = AspisR1.S3S9CurrentSourceModel.s2Row j := by
  rw [rowPrefix_eq_source_s2Row]
  rfl

theorem s2_row_result_value_current (j : Aeneas.Std.Usize) :
    ∃ out, s2_row_result j = .ok out ∧
      out.val = AspisR1.S3S9CurrentSourceModel.s2Row j.val := by
  obtain ⟨out, hout, hvalue⟩ := s2_row_result_value j
  refine ⟨out, hout, ?_⟩
  rw [hvalue]
  rfl

end AspisR1.S3VariantRowAeneasCut
#print axioms AspisR1.S3VariantRowAeneasCut.rowPrefix_eq_current_s2Row
#print axioms AspisR1.S3VariantRowAeneasCut.s2_row_result_value_current
