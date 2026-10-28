import PV_B3P_SelectIndex227
namespace PV_B3P_SelectStep227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_SelectIndex227
set_option autoImplicit false
abbrev Output := Array aspis_core.field.QM31 84#usize

theorem next_value (i : Usize) (hi : i.val < 84) :
    (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  have h : i.val + (1#usize).val < UScalar.size .Usize := by
    have hm := Usize.cMax_bound_concrete.1
    rw [UScalar.size_def]
    scalar_tac
  rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt h]
  rfl

theorem step (claims : Claims) (out : Output) (i : Usize) (hi : i.val < 84) :
    reference_terminal.select227_loop.body claims out i =
      .ok (.cont (out.set i (cell claims i.val hi), Usize.wrapping_add i 1#usize)) := by
  have hb : i < 84#usize := by scalar_tac
  obtain ⟨out',hout',hval⟩ := WP.spec_imp_exists
    (Array.update_spec out i (cell claims i.val hi) (by have h := out.property; scalar_tac))
  simp only [reference_terminal.select227_loop.body,hb,↓reduceIte,
    claim_value claims i hi,hout',hval,lift,bind_tc_ok]

theorem stopped (claims : Claims) (out : Output) (i : Usize) (hi : 84 ≤ i.val) :
    reference_terminal.select227_loop.body claims out i = .ok (.done out) := by
  have hb : ¬ i < 84#usize := by scalar_tac
  simp only [reference_terminal.select227_loop.body,hb,↓reduceIte]

#print axioms next_value
#print axioms step
#print axioms stopped
end PV_B3P_SelectStep227
