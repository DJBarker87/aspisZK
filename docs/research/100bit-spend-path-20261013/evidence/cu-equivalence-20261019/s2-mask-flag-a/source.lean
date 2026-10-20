import CuSavingsS2SourceInactive
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceMaskFlag
open Aeneas Aeneas.Std Result AspisR1S2Groups
variable [Shared]

theorem eq_one (b : Bool) :
    field.QM31.Insts.CoreCmpPartialEqQM31.eq
      (if b then field.QM31.ONE else field.QM31.ZERO) field.QM31.ONE = .ok b := by
  cases b <;> simp [field.QM31.ONE,field.QM31.ZERO,
    field.QM31.Insts.CoreCmpPartialEqQM31.eq,field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    field.M31.Insts.CoreCmpPartialEqM31.eq]

def flag (w : Weights) (j s : Usize) : Result Bool := do
  let prod ← 16#usize*j
  let index ← prod+s
  let q ← Weights.raw w 0#usize index
  field.QM31.Insts.CoreCmpPartialEqQM31.eq q field.QM31.ONE

theorem source_flag (w : Weights) (j s : Usize) (m : U16)
    (hw : w.variant=transport.Variant.S2) (hj : j.val<64) (hs : s.val<16)
    (hm : m.val=CuSavingsS2Tables.masks.getD (CuSavingsS2Tables.groupValue ⟨j.val,hj⟩) 0) :
    flag w j s = .ok (m.val.testBit s.val) := by
  obtain ⟨prod,hp,hpv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=16#usize) (y:=j) (by scalar_tac))
  have h16 : (16#usize).val=16 := by scalar_tac
  rw [h16] at hpv
  obtain ⟨index,hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=prod) (y:=s) (by scalar_tac))
  have hindex : index.val=16*j.val+s.val := by omega
  have hc := (CuSavingsS2Tables.table_correct ⟨j.val,hj⟩ ⟨s.val,hs⟩).2
  change (CuSavingsS2Tables.masks.getD (CuSavingsS2Tables.groupValue ⟨j.val,hj⟩) 0).testBit s.val =
    CuSavingsS2Tables.inactive (16*j.val+s.val) at hc
  rw [←hm] at hc
  have hr := CuSavingsS2SourceInactive.raw_zero w index hw (by omega)
  rw [hindex,←hc] at hr
  simp only [flag,hp,hi,hr,bind_tc_ok,eq_one]

#print axioms eq_one
#print axioms source_flag
end AspisR1.CuSavingsS2SourceMaskFlag
