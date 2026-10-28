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
  cases hp : p.withdrawal <;>
    simp only [hp,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,
      c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]
  -- Explicit splits avoid split_ifs' broad default simplifier.
  all_goals repeat' split
  all_goals first
    | exact ⟨_,rfl⟩
    | apply PV_B3P_FieldResult226V3.no_outer_failure
    | apply PV_B3P_DigestOutcome226V3.no_outer_failure
      · repeat first
          | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
          | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
        scalar_tac
    | apply PV_B3P_FrontierOutcome226V3.no_outer_failure
      · repeat first
          | rw [PV_B3P_NestedOffset226V3.sub_sub_value _ _ _ (by scalar_tac)]
          | rw [PV_B3P_Offset226V3.sub_value _ _ (by scalar_tac)]
        scalar_tac
    | exfalso; scalar_tac

#print axioms no_outer_failure
end PV_B3P_ByteOutcome226V3
