import PV_B3P_ExpandInnerSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem usize_ten_size : 10 < UScalar.size .Usize := by
  have hm := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac

theorem expand_outer_total {N : Usize} (point : Array aspis_core.field.QM31 10#usize)
    (start count : Usize) (n : Nat)
    (hend : (Usize.wrapping_add start count).val ≤ 10)
    (weights : Array aspis_core.field.QM31 N) (len coordinate : Usize)
    (hc : coordinate.val+n = (Usize.wrapping_add start count).val)
    (hcap : len.val*2^n ≤ N.val) :
    Success (reference_copy_terminal.Selectors.expand_loop0 point start count weights len coordinate) := by
  induction n generalizing weights len coordinate with
  | zero =>
    have hb : ¬ coordinate < Usize.wrapping_add start count := by scalar_tac
    unfold reference_copy_terminal.Selectors.expand_loop0
    rw [loop.eq_1]
    simp only [reference_copy_terminal.Selectors.expand_loop0.body,hb,↓reduceIte,lift,bind_tc_ok]
    exact ok _
  | succ n ih =>
    have hb : coordinate < Usize.wrapping_add start count := by scalar_tac
    have hpow : 1 ≤ 2^n := Nat.one_le_pow n 2 (by omega)
    have hcap' : (2*len.val)*2^n ≤ N.val := by
      simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hcap
    have hlen : 2*len.val ≤ N.val := by
      have h := Nat.mul_le_mul_left (2*len.val) hpow
      simp only [Nat.mul_one] at h
      exact le_trans h hcap'
    have hN : N.val < UScalar.size .Usize := by simpa only [UScalar.size] using N.hBounds
    let len1 := Usize.wrapping_mul len 2#usize
    have hlen1 : len1.val = 2*len.val := by
      have h := usize_mul_value len 2#usize (by change len.val*2 < _; omega)
      simpa only [Nat.mul_comm] using h
    let coordinate1 := Usize.wrapping_add coordinate 1#usize
    have hc1 : coordinate1.val = coordinate.val+1 :=
      PV_B3P_Offset226V3.add_value coordinate 1#usize (by
        have h := usize_ten_size
        change coordinate.val+1 < _
        omega)
    obtain ⟨q,hq⟩ := index point coordinate (by change coordinate.val < 10; omega)
    obtain ⟨prepared,hprepared⟩ := total_host_terminal_field_PreparedQm31Multiplier_new q
    obtain ⟨weights1,hweights1⟩ := expand_inner_total weights prepared len hlen
    have hbody : reference_copy_terminal.Selectors.expand_loop0.body point start count
        weights len coordinate = .ok (.cont (weights1,len1,coordinate1)) := by
      simp only [reference_copy_terminal.Selectors.expand_loop0.body,hb,↓reduceIte,
        lift,bind_tc_ok,hq,hprepared,hweights1]
    unfold reference_copy_terminal.Selectors.expand_loop0
    rw [loop.eq_1,hbody]
    exact ih weights1 len1 coordinate1 (by omega) (by simpa only [hlen1] using hcap')

theorem expand_total (N : Usize) (point : Array aspis_core.field.QM31 10#usize)
    (start count : Usize) (hend : start.val+count.val ≤ 10)
    (hcap : 2^count.val ≤ N.val) :
    Success (reference_copy_terminal.Selectors.expand N point start count) := by
  have hpow : 1 ≤ 2^count.val := Nat.one_le_pow count.val 2 (by omega)
  have he : (Usize.wrapping_add start count).val=start.val+count.val :=
    PV_B3P_Offset226V3.add_value start count (by have h := usize_ten_size; omega)
  obtain ⟨weights,hweights⟩ := update (Array.repeat N aspis_core.field.QM31.ZERO)
    0#usize aspis_core.field.QM31.ONE (by change 0<N.val; omega)
  unfold reference_copy_terminal.Selectors.expand
  rw [hweights]
  exact expand_outer_total point start count count.val (by omega) weights 1#usize start
    (by omega) (by simpa only [show (1#usize).val=1 from rfl,Nat.one_mul] using hcap)

theorem selectors_total (point : Array aspis_core.field.QM31 10#usize) :
    Success (reference_copy_terminal.Selectors.at_point point) := by
  unfold reference_copy_terminal.Selectors.at_point
  apply bind
  · exact expand_total 64#usize point 0#usize 6#usize (by change 0+6≤10; omega)
      (by change 64≤64; omega)
  intro high
  apply bind
  · exact expand_total 16#usize point 6#usize 4#usize (by change 6+4≤10; omega)
      (by change 16≤16; omega)
  intro low
  exact ok _

theorem boxed_selectors_total (point : Array aspis_core.field.QM31 10#usize) :
    Success (reference_copy_terminal.Selectors.boxed_at_point point) :=
  selectors_total point

#print axioms usize_ten_size
#print axioms expand_outer_total
#print axioms expand_total
#print axioms selectors_total
#print axioms boxed_selectors_total
end PV_B3P_Success227
