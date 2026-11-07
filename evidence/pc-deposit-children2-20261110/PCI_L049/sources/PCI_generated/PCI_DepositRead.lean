import PCI_DepositRef.Funs
import PCF_ArrayIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositRead

def position (base : Usize) (n : Nat) (bound : base.val+n<80) : Usize :=
  Usize.ofNat (base.val+n) (by scalar_tac)

theorem position_value (base : Usize) (n : Nat) (bound : base.val+n<80) :
    (position base n bound).val=base.val+n := rfl

theorem add_position (base step : Usize) (bound : base.val+step.val<80) :
    base+step=ok (position base step.val bound) := by
  obtain ⟨out,hout,hvalue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=base) (y:=step) (by scalar_tac))
  have he : out=position base step.val bound := by
    apply UScalar.eq_of_val_eq
    simpa only [position_value] using hvalue
  simpa only [he] using hout

def model_word (h : Array U8 80#usize) (offset : Nat) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize
    [h.val[offset]!,h.val[offset+1]!,h.val[offset+2]!,h.val[offset+3]!])

theorem word (h : Array U8 80#usize) (base : Usize) (bound : base.val+3<80) :
    PCI_DepositRef.word h base=ok (model_word h base.val) := by
  have b0 : base.val<h.length := by scalar_tac
  have b1 : base.val+(1#usize).val<80 := by scalar_tac
  have b2 : base.val+(2#usize).val<80 := by scalar_tac
  have b3 : base.val+(3#usize).val<80 := by scalar_tac
  have i1 := PCF_ArrayIndex.result h (position base (1#usize).val b1) (by simp only [position_value];scalar_tac)
  have i2 := PCF_ArrayIndex.result h (position base (2#usize).val b2) (by simp only [position_value];scalar_tac)
  have i3 := PCF_ArrayIndex.result h (position base (3#usize).val b3) (by simp only [position_value];scalar_tac)
  simp only [position_value] at i1 i2 i3
  unfold PCI_DepositRef.word
  rw [PCF_ArrayIndex.result h base b0,add_position base 1#usize b1,
    add_position base 2#usize b2,add_position base 3#usize b3]
  simp only [bind_tc_ok,i1,i2,i3]
  rfl

#print axioms position_value
#print axioms add_position
#print axioms word
end PCI_DepositRead
