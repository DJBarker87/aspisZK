import PV_B3P_Success227
import PV_B3P_P227_00
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_field_accumulate_prepared227 (sums : Array (Array Std.U64 3#usize) 3#usize) (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier) :
    Success (reference_field.accumulate_prepared227 sums right left) := by
  unfold reference_field.accumulate_prepared227
  apply bind
  · apply cadd
  intro right_sum
  apply bind
  · apply add
  intro m
  apply bind
  · apply add
  intro m1
  apply bind
  · apply add
  intro m2
  apply bind
  · apply index <;> scalar_tac
  intro a
  apply bind
  · apply index <;> scalar_tac
  intro m3
  apply bind
  · exact ok _
  intro i
  apply bind
  · apply index <;> scalar_tac
  intro a1
  apply bind
  · apply index <;> scalar_tac
  intro m4
  apply bind
  · exact ok _
  intro i1
  apply bind
  · exact ok _
  intro i2
  apply bind
  · apply index <;> scalar_tac
  intro a2
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · exact ok _
  intro i4
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a3, index_mut_back⟩
  apply bind
  · apply update <;> scalar_tac
  intro a4
  apply bind
  · apply index <;> scalar_tac
  intro m5
  apply bind
  · exact ok _
  intro i5
  apply bind
  · apply index <;> scalar_tac
  intro m6
  apply bind
  · exact ok _
  intro i6
  apply bind
  · exact ok _
  intro i7
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a5
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · exact ok _
  intro i9
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a6, index_mut_back1⟩
  apply bind
  · apply update <;> scalar_tac
  intro a7
  apply bind
  · apply index <;> scalar_tac
  intro m7
  apply bind
  · exact ok _
  intro i10
  apply bind
  · apply index <;> scalar_tac
  intro m8
  apply bind
  · exact ok _
  intro i11
  apply bind
  · exact ok _
  intro i12
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a8
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · exact ok _
  intro i14
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a9, index_mut_back2⟩
  apply bind
  · apply update <;> scalar_tac
  intro a10
  apply bind
  · apply index <;> scalar_tac
  intro a11
  apply bind
  · apply index <;> scalar_tac
  intro m9
  apply bind
  · exact ok _
  intro i15
  apply bind
  · apply index <;> scalar_tac
  intro a12
  apply bind
  · apply index <;> scalar_tac
  intro m10
  apply bind
  · exact ok _
  intro i16
  apply bind
  · exact ok _
  intro i17
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a13
  apply bind
  · apply index <;> scalar_tac
  intro i18
  apply bind
  · exact ok _
  intro i19
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a14, index_mut_back3⟩
  apply bind
  · apply update <;> scalar_tac
  intro a15
  apply bind
  · apply index <;> scalar_tac
  intro m11
  apply bind
  · exact ok _
  intro i20
  apply bind
  · apply index <;> scalar_tac
  intro m12
  apply bind
  · exact ok _
  intro i21
  apply bind
  · exact ok _
  intro i22
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a16
  apply bind
  · apply index <;> scalar_tac
  intro i23
  apply bind
  · exact ok _
  intro i24
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a17, index_mut_back4⟩
  apply bind
  · apply update <;> scalar_tac
  intro a18
  apply bind
  · apply index <;> scalar_tac
  intro m13
  apply bind
  · exact ok _
  intro i25
  apply bind
  · apply index <;> scalar_tac
  intro m14
  apply bind
  · exact ok _
  intro i26
  apply bind
  · exact ok _
  intro i27
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a19
  apply bind
  · apply index <;> scalar_tac
  intro i28
  apply bind
  · exact ok _
  intro i29
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a20, index_mut_back5⟩
  apply bind
  · apply update <;> scalar_tac
  intro a21
  apply bind
  · apply index <;> scalar_tac
  intro a22
  apply bind
  · apply index <;> scalar_tac
  intro m15
  apply bind
  · exact ok _
  intro i30
  apply bind
  · apply index <;> scalar_tac
  intro a23
  apply bind
  · apply index <;> scalar_tac
  intro m16
  apply bind
  · exact ok _
  intro i31
  apply bind
  · exact ok _
  intro i32
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a24
  apply bind
  · apply index <;> scalar_tac
  intro i33
  apply bind
  · exact ok _
  intro i34
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a25, index_mut_back6⟩
  apply bind
  · apply update <;> scalar_tac
  intro a26
  apply bind
  · apply index <;> scalar_tac
  intro m17
  apply bind
  · exact ok _
  intro i35
  apply bind
  · apply index <;> scalar_tac
  intro m18
  apply bind
  · exact ok _
  intro i36
  apply bind
  · exact ok _
  intro i37
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a27
  apply bind
  · apply index <;> scalar_tac
  intro i38
  apply bind
  · exact ok _
  intro i39
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a28, index_mut_back7⟩
  apply bind
  · apply update <;> scalar_tac
  intro a29
  apply bind
  · apply index <;> scalar_tac
  intro m19
  apply bind
  · exact ok _
  intro i40
  apply bind
  · apply index <;> scalar_tac
  intro m20
  apply bind
  · exact ok _
  intro i41
  apply bind
  · exact ok _
  intro i42
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro a30
  apply bind
  · apply index <;> scalar_tac
  intro i43
  apply bind
  · exact ok _
  intro i44
  apply bind
  · apply borrow <;> scalar_tac
  intro pair
  rcases pair with ⟨a31, index_mut_back8⟩
  apply bind
  · apply update <;> scalar_tac
  intro a32
  exact ok _

#print axioms total_reference_field_accumulate_prepared227

end PV_B3P_Success227
