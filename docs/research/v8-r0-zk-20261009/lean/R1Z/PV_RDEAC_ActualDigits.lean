import R1Z.PV_RDEAC_DigitText
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_ActualDigits
open PV_RDEAC_DigitText PV_RDEAC_NibbleBounds

def high (b : U8) : Fin 16 := ⟨(UScalar.cast .Usize (U8.wrapping_shr b 4#u32)).val,high_bound b⟩
def low (b : U8) : Fin 16 := ⟨(UScalar.cast .Usize (b &&& 15#u8)).val,low_bound b⟩

theorem array_lookup {A : Type} {n : Usize} (xs : Array A n) (i : Usize)
    (h : i.val<xs.val.length) :
    Array.index_usize xs i=ok (xs.val[i.val]'h) := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq,List.getElem?_eq_getElem h]

variable [ExternalTypes] [ExternalFuns]
theorem complete (digest : Array U8 32#usize) (i : Usize)
    (h : i.val<digest.val.length) :
    let b := digest.val[i.val]'h
    PV_RDEAC_ActualRound.digits digest i=ok (entry (high b),entry (low b)) := by
  dsimp only
  unfold PV_RDEAC_ActualRound.digits
  rw [array_lookup digest i h]
  simp only [bind_tc_ok,lift]
  change (do
    let hi ← Array.index_usize PV_RDEA_ActualDigitTable.table (UScalar.cast .Usize (U8.wrapping_shr (digest.val[i.val]'h) 4#u32))
    let lo ← Array.index_usize PV_RDEA_ActualDigitTable.table (UScalar.cast .Usize ((digest.val[i.val]'h) &&& 15#u8))
    ok (hi,lo))=_
  rw [lookup _ (high_bound _)]
  simp only [bind_tc_ok]
  rw [lookup _ (low_bound _)]
  rfl

#print axioms array_lookup
#print axioms complete
end R1Z.PV_RDEAC_ActualDigits
