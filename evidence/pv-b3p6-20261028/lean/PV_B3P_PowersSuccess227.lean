import PV_B3P_Success227
import PV_B3P_E227_15
import PV_B3P_Offset226V3
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- Success of the actual power-building loop, with its array bound and
strictly decreasing remaining-limb count. Field words remain symbolic. -/
theorem pattern_powers_total (lambda : aspis_core.field.QM31)
    (powers : Array aspis_core.field.QM31 16#usize)
    (power : aspis_core.field.QM31) (limb : Usize) (hl : limb.val≤16) :
    Success (reference_copy_terminal.pattern_values_literal_loop0 lambda powers power limb) := by
  have hw : aspis_statement.poseidon2.POSEIDON2_WIDTH=16#usize := by
    unfold aspis_statement.poseidon2.POSEIDON2_WIDTH
    rfl
  unfold reference_copy_terminal.pattern_values_literal_loop0
  refine loop_total _ (fun x : Array aspis_core.field.QM31 16#usize × aspis_core.field.QM31 × Usize => 16-x.2.2.val)
    (fun x => x.2.2.val≤16) ?_ (powers,power,limb) hl
  rintro ⟨values,pow,i⟩ hi
  change i.val≤16 at hi
  by_cases hp : i.val<16
  · have hb : i<16#usize := by scalar_tac
    obtain ⟨values1,hvalues1⟩ := update values i pow hp
    obtain ⟨pow1,hpow1⟩ := qmul pow lambda
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    refine ⟨.cont (values1,pow1,j),?_,?_,?_⟩
    · simp only [reference_copy_terminal.pattern_values_literal_loop0.body,hw,hb,↓reduceIte,
        hvalues1,hpow1,lift,bind_tc_ok,j]
    · change j.val≤16
      omega
    · change 16-j.val<16-i.val
      omega
  · have hb : ¬i<16#usize := by scalar_tac
    refine ⟨.done (values,i),?_,True.intro⟩
    simp only [reference_copy_terminal.pattern_values_literal_loop0.body,hw,hb,↓reduceIte]

#print axioms pattern_powers_total
end PV_B3P_Success227
