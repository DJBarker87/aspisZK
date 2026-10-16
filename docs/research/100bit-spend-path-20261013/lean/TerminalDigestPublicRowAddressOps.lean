import TerminalDigestPublicLoopSource
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.RowAddressOps
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev Usize := UScalar UScalarTy.Usize

private theorem small_max (n : Nat) (hn : n < 2048) : n ≤ Usize.max := by
  have hpow : n < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  have hsucc : n < Usize.max + 1 := by
    simpa only [UScalarTy.Usize_numBits_eq, Usize.max_succ_eq_pow] using hpow
  omega

private theorem add_exact (a b : Usize) (hbound : a.val + b.val ≤ Usize.max) :
    ∃ out : Usize, (a + b : Result Usize) = .ok out ∧ out.val = a.val + b.val := by
  have hchecked : (a + b : Result Usize) ⦃z => z.val = a.val + b.val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hbound
  obtain ⟨out, hrun, hval⟩ := WP.spec_imp_exists hchecked
  exact ⟨out, hrun, hval⟩

private theorem mul_exact (a b : Usize) (hbound : a.val * b.val ≤ Usize.max) :
    ∃ out : Usize, (a * b : Result Usize) = .ok out ∧ out.val = a.val * b.val := by
  have hchecked : (a * b : Result Usize) ⦃z => z.val = a.val * b.val⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using hbound
  obtain ⟨out, hrun, hval⟩ := WP.spec_imp_exists hchecked
  exact ⟨out, hrun, hval⟩

/-- The outer digest loop's literal checked row-address operations always
succeed for a bounded frontier level, with exact natural row formulas. -/
theorem source_row_addresses (level : Usize) (hlevel : level.val < 20) :
    ∃ block base plus : Usize,
      (34#usize + level : Result Usize) = .ok block ∧
      block.val = 34 + level.val ∧
      (block * 16#usize : Result Usize) = .ok base ∧
      base.val = (34 + level.val) * 16 ∧
      (base + 12#usize : Result Usize) = .ok plus ∧
      plus.val = (34 + level.val) * 16 + 12 := by
  have h34 : (34#usize).val = 34 := by scalar_tac
  have h16 : (16#usize).val = 16 := by scalar_tac
  have h12 : (12#usize).val = 12 := by scalar_tac
  obtain ⟨block, hblock, hvblock⟩ := add_exact (34#usize) level (by
    have hb := small_max (34 + level.val) (by omega)
    simpa [h34] using hb)
  obtain ⟨base, hbase, hvbase⟩ := mul_exact block (16#usize) (by
    have hb := small_max ((34 + level.val) * 16) (by omega)
    simpa [hvblock, h16] using hb)
  obtain ⟨plus, hplus, hvplus⟩ := add_exact base (12#usize) (by
    have hb := small_max ((34 + level.val) * 16 + 12) (by omega)
    simpa [hvbase, hvblock, h16, h12] using hb)
  refine ⟨block, base, plus, hblock, ?_, hbase, ?_, hplus, ?_⟩
  · calc
      block.val = (34#usize).val + level.val := hvblock
      _ = 34 + level.val := by rw [h34]
  · calc
      base.val = block.val * (16#usize).val := hvbase
      _ = (34 + level.val) * 16 := by rw [hvblock, h16, h34]
  · calc
      plus.val = base.val + (12#usize).val := hvplus
      _ = (34 + level.val) * 16 + 12 := by rw [hvbase, hvblock, h16, h12, h34]

#print axioms source_row_addresses
end AspisR1TerminalDigestPublicLoop.RowAddressOps
