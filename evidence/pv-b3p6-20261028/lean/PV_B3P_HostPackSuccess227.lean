import PV_B3P_Success227
import PV_B3P_PackLoopSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_host_terminal_field_qm31_pack_base4 (values : Slice aspis_core.field.QM31) (hlen : (Slice.len values).val ≤ 4) :
    Success (host_terminal_field.qm31_pack_base4 values) := by
  unfold host_terminal_field.qm31_pack_base4
  have hb : Slice.len values ≤ 4#usize := by scalar_tac
  simp only [massert,hb,↓reduceIte,bind_tc_ok]
  apply bind
  · apply host_pack_loop_total <;> scalar_tac
  intro padded1
  apply bind
  · apply index <;> scalar_tac
  intro v0
  apply bind
  · apply index <;> scalar_tac
  intro v1
  apply bind
  · apply index <;> scalar_tac
  intro v2
  apply bind
  · apply index <;> scalar_tac
  intro v3
  apply bind
  · exact ok _
  intro p
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i1
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i2
  apply bind
  · exact ok _
  intro i3
  apply bind
  · exact ok _
  intro i4
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i5
  apply bind
  · exact ok _
  intro i6
  apply bind
  · exact ok _
  intro i7
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i8
  apply bind
  · exact ok _
  intro i9
  apply bind
  · exact ok _
  intro i10
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i11
  apply bind
  · exact ok _
  intro i12
  apply bind
  · exact ok _
  intro i13
  apply bind
  · exact ok _
  intro i14
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i15
  apply bind
  · exact ok _
  intro i16
  apply bind
  · exact ok _
  intro i17
  apply bind
  · exact ok _
  intro c0_a
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i18
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i19
  apply bind
  · exact ok _
  intro i20
  apply bind
  · exact ok _
  intro i21
  apply bind
  · exact ok _
  intro i22
  apply bind
  · exact ok _
  intro i23
  apply bind
  · exact ok _
  intro i24
  apply bind
  · exact ok _
  intro i25
  apply bind
  · exact ok _
  intro i26
  apply bind
  · exact ok _
  intro c0_b
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i27
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i28
  apply bind
  · exact ok _
  intro i29
  apply bind
  · exact ok _
  intro i30
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i31
  apply bind
  · exact ok _
  intro i32
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i33
  apply bind
  · exact ok _
  intro i34
  apply bind
  · exact ok _
  intro c1_a
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i35
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i36
  apply bind
  · exact ok _
  intro i37
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i38
  apply bind
  · exact ok _
  intro i39
  apply bind
  · apply total_host_terminal_field_terminal_limb
  intro i40
  apply bind
  · exact ok _
  intro c1_b
  apply bind
  · apply reduce64
  intro m
  apply bind
  · apply reduce64
  intro m1
  apply bind
  · apply cnew
  intro c
  apply bind
  · apply reduce64
  intro m2
  apply bind
  · apply reduce64
  intro m3
  apply bind
  · apply cnew
  intro c1
  exact ok _

#print axioms total_host_terminal_field_qm31_pack_base4

end PV_B3P_Success227
