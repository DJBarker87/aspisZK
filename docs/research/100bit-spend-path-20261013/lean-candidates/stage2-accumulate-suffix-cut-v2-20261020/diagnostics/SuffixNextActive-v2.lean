import Aeneas
import AspisR1Stage2Accumulate.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2Accumulate.QueryAdvance

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem exact_suffix_increment_active
    (a : verifier.Accumulator) (newPower : aspis_core.field.QM31)
    (out : verifier.Accumulator) (hactive : a.next < 22#usize)
    (h : verifier.accumulate_suffix a newPower = .ok out) :
    out.next.val = a.next.val + 1 := by
  unfold verifier.accumulate_suffix at h
  obtain ⟨i, hadd, hstate⟩ := bind_success _ _ _ h
  have hactiveNat : a.next.val < 22 := by
    simpa only [UScalar.lt_equiv] using hactive
  have hspec : a.next + 1#usize ⦃ j => j.val = a.next.val + 1 ⦄ := by
    apply Usize.add_spec
    scalar_tac
  obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists hspec
  have hij : i = j := Result.ok.inj (hadd.symm.trans hj)
  have hrec := Result.ok.inj hstate
  have hnext : i = out.next := by
    simpa using congrArg (fun acc : verifier.Accumulator => acc.next) hrec
  calc
    out.next.val = i.val := congrArg Usize.val hnext.symm
    _ = j.val := congrArg Usize.val hij
    _ = a.next.val + 1 := hjval

#print axioms exact_suffix_increment_active

end AspisR1Stage2Accumulate.QueryAdvance
