import PV_B3P_DigestOutcome226V3
import PV_B3P_FrontierOutcome226V3
import PV_B3P_Offset226V3
import PV_B3P_NestedOffset226V3
namespace PV_B3P_ByteOutcome226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem no_outer_failure (p : reference226.OwnedPublic) (i : Usize) :
    ∃ v, reference226.byte_at p i = .ok v := by
  have c0 : Usize.wrapping_add 70#usize 32#usize = 102#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c1 : Usize.wrapping_add 102#usize 32#usize = 134#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c2 : Usize.wrapping_add 70#usize 33#usize = 103#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c3 : Usize.wrapping_add 102#usize 33#usize = 135#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c4 : Usize.wrapping_add 107#usize 8#usize = 115#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c5 : Usize.wrapping_add 135#usize 8#usize = 143#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c6 : Usize.wrapping_add 115#usize 640#usize = 755#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c7 : Usize.wrapping_add 143#usize 640#usize = 783#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c8 : Usize.wrapping_add 115#usize 672#usize = 787#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  have c9 : Usize.wrapping_add 143#usize 672#usize = 815#usize := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value]
    · rfl
    · have hb := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac
  unfold reference226.byte_at
  cases hp : p.withdrawal with
  | false =>
    simp only [hp,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,
      c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
    by_cases h0 : i ≥ 1455#usize
    · simp only [h0,↓reduceIte]
      exact ⟨_,rfl⟩
    · simp only [h0,↓reduceIte]
      by_cases h1 : i = 0#usize
      · simp only [h1,↓reduceIte]
        exact ⟨_,rfl⟩
      · simp only [h1,↓reduceIte]
        by_cases h2 : i < 33#usize
        · simp only [h2,↓reduceIte]
          apply PV_B3P_DigestOutcome226V3.no_outer_failure
          · repeat first
              | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
              | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
            scalar_tac
        · simp only [h2,↓reduceIte]
          by_cases h3 : i < 65#usize
          · simp only [h3,↓reduceIte]
            apply PV_B3P_DigestOutcome226V3.no_outer_failure
            · repeat first
                | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
              scalar_tac
          · simp only [h3,↓reduceIte]
            by_cases h4 : i < 69#usize
            · simp only [h4,↓reduceIte]
              exact PV_B3P_FieldResult226V3.no_outer_failure _ _
            · simp only [h4,↓reduceIte]
              by_cases h5 : i = 69#usize
              · simp only [h5,↓reduceIte]
                exact ⟨_,rfl⟩
              · simp only [h5,↓reduceIte]
                by_cases h6 : i < 102#usize
                · simp only [h6,↓reduceIte]
                  apply PV_B3P_DigestOutcome226V3.no_outer_failure
                  · repeat first
                      | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                      | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                    scalar_tac
                · simp only [h6,↓reduceIte]
                  by_cases h7 : i < 134#usize
                  · simp only [h7,↓reduceIte]
                    apply PV_B3P_DigestOutcome226V3.no_outer_failure
                    · repeat first
                        | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                        | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                      scalar_tac
                  · simp only [h7,↓reduceIte]
                    by_cases h8 : i = 134#usize
                    · simp only [h8,↓reduceIte]
                      exact ⟨_,rfl⟩
                    · simp only [h8,↓reduceIte]
                      by_cases h9 : i < 135#usize
                      · simp only [h9,↓reduceIte]
                        exfalso; scalar_tac
                      · simp only [h9,↓reduceIte]
                        by_cases h10 : i < 143#usize
                        · simp only [h10,↓reduceIte]
                          exact ⟨_,rfl⟩
                        · simp only [h10,↓reduceIte]
                          by_cases h11 : i < 783#usize
                          · simp only [h11,↓reduceIte]
                            apply PV_B3P_FrontierOutcome226V3.no_outer_failure
                            · repeat first
                                | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                                | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                              scalar_tac
                          · simp only [h11,↓reduceIte]
                            by_cases h12 : i < 815#usize
                            · simp only [h12,↓reduceIte]
                              apply PV_B3P_DigestOutcome226V3.no_outer_failure
                              · repeat first
                                  | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                                  | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                                scalar_tac
                            · simp only [h12,↓reduceIte]
                              apply PV_B3P_FrontierOutcome226V3.no_outer_failure
                              · repeat first
                                  | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                                  | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                                scalar_tac
  | true =>
    simp only [hp,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,
      c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
    by_cases h0 : i ≥ 1427#usize
    · simp only [h0,↓reduceIte]
      exact ⟨_,rfl⟩
    · simp only [h0,↓reduceIte]
      by_cases h1 : i = 0#usize
      · simp only [h1,↓reduceIte]
        exact ⟨_,rfl⟩
      · simp only [h1,↓reduceIte]
        by_cases h2 : i < 33#usize
        · simp only [h2,↓reduceIte]
          apply PV_B3P_DigestOutcome226V3.no_outer_failure
          · repeat first
              | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
              | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
            scalar_tac
        · simp only [h2,↓reduceIte]
          by_cases h3 : i < 65#usize
          · simp only [h3,↓reduceIte]
            apply PV_B3P_DigestOutcome226V3.no_outer_failure
            · repeat first
                | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
              scalar_tac
          · simp only [h3,↓reduceIte]
            by_cases h4 : i < 69#usize
            · simp only [h4,↓reduceIte]
              exact PV_B3P_FieldResult226V3.no_outer_failure _ _
            · simp only [h4,↓reduceIte]
              by_cases h5 : i = 69#usize
              · simp only [h5,↓reduceIte]
                exact ⟨_,rfl⟩
              · simp only [h5,↓reduceIte]
                by_cases h6 : i < 70#usize
                · simp only [h6,↓reduceIte]
                  exfalso; scalar_tac
                · simp only [h6,↓reduceIte]
                  by_cases h7 : i < 102#usize
                  · simp only [h7,↓reduceIte]
                    apply PV_B3P_DigestOutcome226V3.no_outer_failure
                    · repeat first
                        | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                        | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                      scalar_tac
                  · simp only [h7,↓reduceIte]
                    by_cases h8 : i = 102#usize
                    · simp only [h8,↓reduceIte]
                      exact ⟨_,rfl⟩
                    · simp only [h8,↓reduceIte]
                      by_cases h9 : i < 107#usize
                      · simp only [h9,↓reduceIte]
                        exact PV_B3P_FieldResult226V3.no_outer_failure _ _
                      · simp only [h9,↓reduceIte]
                        by_cases h10 : i < 115#usize
                        · simp only [h10,↓reduceIte]
                          exact ⟨_,rfl⟩
                        · simp only [h10,↓reduceIte]
                          by_cases h11 : i < 755#usize
                          · simp only [h11,↓reduceIte]
                            apply PV_B3P_FrontierOutcome226V3.no_outer_failure
                            · repeat first
                                | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                                | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                              scalar_tac
                          · simp only [h11,↓reduceIte]
                            by_cases h12 : i < 787#usize
                            · simp only [h12,↓reduceIte]
                              apply PV_B3P_DigestOutcome226V3.no_outer_failure
                              · repeat first
                                  | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                                  | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                                scalar_tac
                            · simp only [h12,↓reduceIte]
                              apply PV_B3P_FrontierOutcome226V3.no_outer_failure
                              · repeat first
                                  | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
                                  | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
                                scalar_tac

#print axioms no_outer_failure
end PV_B3P_ByteOutcome226V3
