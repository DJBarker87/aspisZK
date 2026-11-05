import NHE_ScalePort
set_option autoImplicit false
namespace NHE_RoundAddresses
open Aeneas Aeneas.Std Result AspisR1

theorem total (round : Usize) (small : round.val<2) :
 ∃ i,3#usize*round=ok i ∧ (i+1#usize)=ok (Usize.wrapping_add i 1#usize) ∧
 (i+2#usize)=ok (Usize.wrapping_add i 2#usize) := by
 have cap : 16<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 let i := UScalar.wrapping_mul 3#usize round
 have hi : 3#usize*round=ok i := FIo_ScalarBridge.mul _ _ (by change 3*round.val<UScalar.size .Usize;omega)
 have iv : i.val=3*round.val := by
  unfold i
  rw [UScalar.wrapping_mul_val_eq,Nat.mod_eq_of_lt (by change 3*round.val<UScalar.size .Usize;omega)]
  rfl
 exact ⟨i,hi,FIo_ScalarBridge.add _ _ (by change i.val+1<UScalar.size .Usize;rw [iv];omega),FIo_ScalarBridge.add _ _ (by change i.val+2<UScalar.size .Usize;rw [iv];omega)⟩

#print axioms total
end NHE_RoundAddresses
