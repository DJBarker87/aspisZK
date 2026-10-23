import R1Z.ProverCommitInactiveRow49
import R1Z.ProverCommitInactiveTable49
import R1Z.ProverCommitSampleTail49
/-! Complete inactive-kind source owner equals the model's inactive indicator. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInactiveModel49
open Aeneas Aeneas.Std Result AspisR1InactiveOwner49
open ProverCommitInactiveRow49 ProverCommitInactiveTable49
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def row (j : Usize) : Fin 1024 := ⟨AspisR1.rowNat j.val,AspisR1.rowNat_lt j.val⟩

theorem inactive_exact (j : Usize) :
    owned.inactive j=ok (decide (row j ∈ R0P.copyInactiveRows)) := by
  obtain ⟨r,hr,hvr⟩ := row_exact j
  obtain ⟨idx,hidx,hvidx⟩ := div_value r 16#usize (by decide)
  obtain ⟨bit,hbit,hvbit⟩ := rem_value r 16#usize (by decide)
  have hrsmall : r.val<1024 := by rw [hvr];exact AspisR1.rowNat_lt j.val
  have hidxsmall : idx.val<64 := by rw [hvidx];change r.val/16<64;omega
  have hbitsmall : bit.val<16 := by rw [hvbit];exact Nat.mod_lt _ (by decide)
  have hcast : (UScalar.cast .U32 bit).val=bit.val := by scalar_tac
  rw [owned.inactive,hr]
  simp only [bind_tc_ok,hidx,table_index idx hidxsmall,hbit,lift]
  simp only [zero_iff _ _ (by rw [hcast];omega)]
  have hfin : (⟨idx.val,hidxsmall⟩ : Fin 64)=
      ⟨AspisR1.rowNat j.val/16,by have := AspisR1.rowNat_lt j.val;omega⟩ := by
    apply Fin.ext
    change idx.val=AspisR1.rowNat j.val/16
    rw [hvidx,hvr]
    rfl
  rw [table_value,hfin,hcast,hvbit,hvr]
  change ok (decide ((R0P.copyActiveRowMasks ⟨AspisR1.rowNat j.val/16,by omega⟩).testBit
    (AspisR1.rowNat j.val%16)=false))=_
  simp only [R0P.copyInactiveRows,Finset.mem_filter,Finset.mem_univ,true_and,R0P.CopyActiveRow,row]
  cases (R0P.copyActiveRowMasks ⟨AspisR1.rowNat j.val/16,by have := AspisR1.rowNat_lt j.val;omega⟩).testBit
    (AspisR1.rowNat j.val%16) <;> rfl

theorem row_model (j : Usize) (hj : j.val<1024) : row j=AspisR1.rowEquiv.symm ⟨j.val,hj⟩ := by
  apply AspisR1.rowEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change AspisR1.rowNat (AspisR1.rowNat j.val)=j.val
  exact AspisR1.rowNat_involutive j.val hj

def raw (j : Usize) : Old.Q := if row j ∈ R0P.copyInactiveRows then ProverCommitSubtraction47.one else zero

theorem raw_canonical (j : Usize) : Canonical (raw j) := by
  unfold raw
  split
  · exact ProverCommitSubtraction47.one_canonical
  · exact zero_canonical

theorem raw_value (j : Usize) (hj : j.val<1024) :
    decode (raw j)=AspisR0.Opening.indicator R0P.copyInactiveRows (AspisR1.rowEquiv.symm ⟨j.val,hj⟩) := by
  rw [raw,row_model j hj]
  unfold AspisR0.Opening.indicator
  split <;> simp only [ProverCommitSubtraction47.one_decode,zero_decode]

#print axioms inactive_exact
#print axioms row_model
#print axioms raw_canonical
#print axioms raw_value
end R1Z.ProverCommitInactiveModel49
