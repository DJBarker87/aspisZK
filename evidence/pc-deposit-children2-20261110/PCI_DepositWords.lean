import PCI_DepositRead
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositWords
open PCI_DepositRead

def model (h : Array U8 80#usize) (base : Nat) : Array U32 8#usize :=
  Array.make 8#usize [model_word h (base+0), model_word h (base+4), model_word h (base+8), model_word h (base+12), model_word h (base+16), model_word h (base+20), model_word h (base+24), model_word h (base+28)]

theorem words (h : Array U8 80#usize) (base : Usize) (bound : base.val+31<80) :
    PCI_DepositRef.words h base=ok (model h base.val) := by
  have b0 : base.val+(0#usize).val<80 := by scalar_tac
  have w0 := PCI_DepositRead.word h (position base (0#usize).val b0) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w0
  have b1 : base.val+(4#usize).val<80 := by scalar_tac
  have w1 := PCI_DepositRead.word h (position base (4#usize).val b1) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w1
  have b2 : base.val+(8#usize).val<80 := by scalar_tac
  have w2 := PCI_DepositRead.word h (position base (8#usize).val b2) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w2
  have b3 : base.val+(12#usize).val<80 := by scalar_tac
  have w3 := PCI_DepositRead.word h (position base (12#usize).val b3) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w3
  have b4 : base.val+(16#usize).val<80 := by scalar_tac
  have w4 := PCI_DepositRead.word h (position base (16#usize).val b4) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w4
  have b5 : base.val+(20#usize).val<80 := by scalar_tac
  have w5 := PCI_DepositRead.word h (position base (20#usize).val b5) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w5
  have b6 : base.val+(24#usize).val<80 := by scalar_tac
  have w6 := PCI_DepositRead.word h (position base (24#usize).val b6) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w6
  have b7 : base.val+(28#usize).val<80 := by scalar_tac
  have w7 := PCI_DepositRead.word h (position base (28#usize).val b7) (by simp only [position_value];scalar_tac)
  simp only [position_value] at w7
  unfold PCI_DepositRef.words
  rw [add_position base 0#usize b0, add_position base 4#usize b1, add_position base 8#usize b2, add_position base 12#usize b3, add_position base 16#usize b4, add_position base 20#usize b5, add_position base 24#usize b6, add_position base 28#usize b7]
  simp only [bind_tc_ok,w0, w1, w2, w3, w4, w5, w6, w7]
  rfl

#print axioms words
end PCI_DepositWords
