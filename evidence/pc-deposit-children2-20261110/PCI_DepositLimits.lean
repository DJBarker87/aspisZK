import PCI_DepositActual.Funs
import PCI_SizeArithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositLimits
open PCI_DepositActual

theorem maximum : deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES=ok 592#usize := by
  unfold deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES
  unfold aspis_statement.pool_v1.deposit.POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES
  unfold deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
  have hc : Usize.checked_add 80#usize 512#usize=some 592#usize := by
    have h := PCI_SizeArithmetic.checked 80#usize 512#usize (by scalar_tac)
    have hv : PCI_SizeArithmetic.sum 80#usize 512#usize (by scalar_tac)=592#usize := by
      apply UScalar.eq_of_val_eq
      rfl
    simpa only [hv] using h
  simp only [bind_tc_ok,hc,lift,pure]

theorem short (bytes : Slice U8) (magic : Array U8 4#usize)
    (bound : bytes.length<80) :
    deposit_transport.decode_deposit_instruction_with_magic_v1 bytes magic=
      ok (.Err deposit_transport.DepositInstructionFormatErrorV1.WrongLength) := by
  have h : Slice.len bytes<deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES := by
    unfold deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
    scalar_tac
  simp only [deposit_transport.decode_deposit_instruction_with_magic_v1,h,ite_true]

theorem long (bytes : Slice U8) (magic : Array U8 4#usize)
    (bound : bytes.length>592) :
    deposit_transport.decode_deposit_instruction_with_magic_v1 bytes magic=
      ok (.Err deposit_transport.DepositInstructionFormatErrorV1.WrongLength) := by
  have h : ¬Slice.len bytes<deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES := by
    unfold deposit_transport.POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
    scalar_tac
  have hlong : Slice.len bytes>592#usize := by scalar_tac
  simp only [deposit_transport.decode_deposit_instruction_with_magic_v1,h,ite_false,maximum,bind_tc_ok,hlong,ite_true]

#print axioms maximum
#print axioms short
#print axioms long
end PCI_DepositLimits
