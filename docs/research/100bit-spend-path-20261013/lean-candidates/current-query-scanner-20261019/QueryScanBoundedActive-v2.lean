import QueryScanActiveStep
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

private theorem usize_add_one_small (a : Std.Usize) (ha : a.val < 64) :
    ∃ b : Std.Usize, (a + 1#usize : Result Std.Usize) = .ok b ∧ b.val = a.val + 1 := by
  have hb : a.val + 1 ≤ Usize.max := by
    have hm := Usize.cMax_bound_concrete.1
    omega
  have hs : (a + 1#usize : Result Std.Usize) ⦃ b => b.val = a.val + 1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using (show a.val + (1#usize).val ≤ Usize.max by simpa using hb)
  obtain ⟨b, hab, hv⟩ := Aeneas.Std.WP.spec_imp_exists hs
  exact ⟨b, hab, hv⟩

theorem active_q22_of_bounded_source (s : QueryScan)
    (hlen : s.accepted_len.val < 22) (hdraws : s.draws.val < 64) :
    (q22StateOfFresh s).accepted.length ≠ 22 ∧
      (q22StateOfFresh s).draws ≠ 64 := by
  constructor
  · intro he
    have hp : (s.accepted.val.take s.accepted_len.val).length ≤ s.accepted_len.val := by
      exact List.length_take_le _ _
    have hval : (q22StateOfFresh s).accepted.length =
        (s.accepted.val.take s.accepted_len.val).length := by
      simp [q22StateOfFresh, acceptedPrefix]
    omega
  · simp [q22StateOfFresh]
    omega

theorem source_draw_increment_success (s : QueryScan)
    (hdraws : s.draws.val < 64) :
    ∃ d : Std.Usize, (s.draws + 1#usize : Result Std.Usize) = .ok d ∧ d.val = s.draws.val + 1 :=
  usize_add_one_small s.draws hdraws

theorem source_length_increment_success (s : QueryScan)
    (hlen : s.accepted_len.val < 22) :
    ∃ n : Std.Usize, (s.accepted_len + 1#usize : Result Std.Usize) = .ok n ∧
      n.val = s.accepted_len.val + 1 := by
  apply usize_add_one_small
  omega

#print axioms active_q22_of_bounded_source
#print axioms source_draw_increment_success
#print axioms source_length_increment_success
end AspisR1QueryScanUnrolled.r0_transcript
