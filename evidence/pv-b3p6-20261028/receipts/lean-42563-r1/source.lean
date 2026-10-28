import PV_B3P_WordLaw226V3
import PV_B3P_EndianVerified226V3
import PV_B3P_ResultSuccess226
namespace PV_B3P_NativeFieldByte226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false

theorem complete_result (v : U32) (j : Usize) (hj : j.val < 4) :
    reference226.field_byte v j =
      if v < 2147483647#u32 then .ok (.Ok
        ((core.num.U32.to_le_bytes v).val[j.val]'(by
          have hlen := (core.num.U32.to_le_bytes v).property
          rw [hlen]
          simpa using hj)))
      else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public) := by
  by_cases h : v < 2147483647#u32
  · rw [if_pos h]
    have hf : PV_B3P_WordLaw226V3.four v = .ok (.Ok (wordBytes v)) := by
      rw [PV_B3P_WordLaw226V3.complete_word,if_pos h]
    unfold PV_B3P_WordLaw226V3.four at hf
    rw [PV_B3P_ResultSuccess226.bind_success] at hf
    obtain ⟨b0,h0,ht0⟩ := hf
    rw [PV_B3P_ResultSuccess226.bind_success] at ht0
    obtain ⟨b1,h1,ht1⟩ := ht0
    rw [PV_B3P_ResultSuccess226.bind_success] at ht1
    obtain ⟨b2,h2,ht2⟩ := ht1
    rw [PV_B3P_ResultSuccess226.bind_success] at ht2
    obtain ⟨b3,h3,ht3⟩ := ht2
    have he : [b0,b1,b2,b3] = wordBytes v :=
      core.result.Result.Ok.inj (Result.ok.inj ht3)
    have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases hcases with hj0 | hj1 | hj2 | hj3
    · have hje : j = 0#usize := by apply UScalar.eq_of_val_eq; exact hj0
      subst j
      have hv : (0#usize).val = 0 := rfl
      simpa only [hv,← PV_B3P_EndianVerified226V3.word_bytes,← he,
        List.getElem_cons_zero,List.getElem_cons_succ] using h0
    · have hje : j = 1#usize := by apply UScalar.eq_of_val_eq; exact hj1
      subst j
      have hv : (1#usize).val = 1 := rfl
      simpa only [hv,← PV_B3P_EndianVerified226V3.word_bytes,← he,
        List.getElem_cons_zero,List.getElem_cons_succ] using h1
    · have hje : j = 2#usize := by apply UScalar.eq_of_val_eq; exact hj2
      subst j
      have hv : (2#usize).val = 2 := rfl
      simpa only [hv,← PV_B3P_EndianVerified226V3.word_bytes,← he,
        List.getElem_cons_zero,List.getElem_cons_succ] using h2
    · have hje : j = 3#usize := by apply UScalar.eq_of_val_eq; exact hj3
      subst j
      have hv : (3#usize).val = 3 := rfl
      simpa only [hv,← PV_B3P_EndianVerified226V3.word_bytes,← he,
        List.getElem_cons_zero,List.getElem_cons_succ] using h3
  · rw [if_neg h]
    exact PV_B3P_ByteScalar226V3.field_reject v j h

#print axioms complete_result
end PV_B3P_NativeFieldByte226V3
