import CuSavingsS2SourceRow
import CuSavingsS2SourceTables
import CuSavingsS2Tables
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceInactive
open Aeneas Aeneas.Std Result AspisR1S2Groups

theorem inactive_source (r : Usize) (hrange : r.val < 1024) :
    ∃ b : Bool, r0.opening.inactive r = .ok (.Ok b) ∧
      b = !(CuSavingsS2Tables.active.getD (r.val/16) 0).testBit (r.val%16) := by
  have h16 : (16#usize).val=16 := by scalar_tac
  have h1024 : (1024#usize).val=1024 := by scalar_tac
  have h0 : (0#u16).val=0 := by decide
  have h1 : (1#u16).val=1 := by decide
  obtain ⟨quot,hq,hqv⟩ := WP.spec_imp_exists (UScalar.div_spec r (y:=16#usize) (by scalar_tac))
  rw [h16] at hqv
  obtain ⟨mask,hm,hmv⟩ := CuSavingsS2SourceTables.active_source quot (by omega)
  obtain ⟨rem,hr,hrv⟩ := WP.spec_imp_exists (UScalar.rem_spec r (y:=16#usize) (by scalar_tac))
  rw [h16] at hrv
  obtain ⟨shifted,hs,hsv,_⟩ := WP.spec_imp_exists (U16.ShiftRight_spec mask rem (by omega))
  let bits := shifted &&& 1#u16
  have hb : bits.val = (CuSavingsS2Tables.active.getD (r.val/16) 0 >>> (r.val%16)) &&& 1 := by
    simp only [bits,UScalar.val_and,h1,hsv,hmv,hqv,hrv]
  have hcond : ¬ r >= 1024#usize := by simpa only [UScalar.le_equiv,h1024] using (by omega : ¬ 1024 ≤ r.val)
  refine ⟨decide (bits=0#u16),?_,?_⟩
  · simp only [r0.opening.inactive,if_neg hcond,hq,hm,hr,hs,bind_tc_ok,lift]
    rfl
  · have heq : (bits=0#u16) ↔ ((CuSavingsS2Tables.active.getD (r.val/16) 0 >>> (r.val%16)) &&& 1)=0 := by
      constructor
      · intro h;have hv:=congrArg UScalar.val h;rw [hb,h0] at hv;exact hv
      · intro h;apply UScalar.eq_of_val_eq;simpa only [hb,h0] using h
    simp only [heq,Nat.testBit,Nat.and_comm]
    simp

theorem raw_zero [Shared] (w : Weights) (j : Usize) (hw : w.variant=transport.Variant.S2)
    (hj : j.val < 1024) :
    Weights.raw w 0#usize j = .ok
      (if CuSavingsS2Tables.inactive j.val then field.QM31.ONE else field.QM31.ZERO) := by
  obtain ⟨row,hr,hv⟩ := CuSavingsS2SourceRow.source_s2 j
  have hrow : row.val < 1024 := by
    have h := (CuSavingsS2Tables.table_correct ⟨j.val/16,by omega⟩ ⟨j.val%16,by omega⟩).1
    have hindex : 16*(j.val/16)+j.val%16=j.val := by omega
    rw [hindex,←hv] at h
    exact h
  obtain ⟨b,hb,hbv⟩ := inactive_source row hrow
  have bval : b=CuSavingsS2Tables.inactive j.val := by
    simpa only [CuSavingsS2Tables.inactive,hv] using hbv
  simp only [Weights.raw,hw,hr,hb,bind_tc_ok,core.result.Result.unwrap,bval]

#print axioms inactive_source
#print axioms raw_zero
end AspisR1.CuSavingsS2SourceInactive
