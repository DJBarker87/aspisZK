import NEC_TransferDecode
import NEC_WithdrawalDecode
import NEC_SliceDomains
set_option autoImplicit false
namespace NEC_PaymentDomains
open Aeneas Aeneas.Std

def TransferDomain (_common : NEC_TransferDecode.Common) (bytes : Slice U8) : Prop := bytes.val.length=216

def WithdrawalDomain (_common : NEC_WithdrawalDecode.Common) (bytes : Slice U8) : Prop := bytes.val.length=216

theorem transfer_caller (common : NEC_TransferDecode.Common) (parent child : Slice U8)
 (length : parent.val.length=1880) (association : child.val=parent.val.drop 1664) : TransferDomain common child := by
 unfold TransferDomain
 rw [association]
 exact NEC_SliceDomains.terminal_payment _ length

theorem withdrawal_caller (common : NEC_WithdrawalDecode.Common) (parent child : Slice U8)
 (length : parent.val.length=1880) (association : child.val=parent.val.drop 1664) : WithdrawalDomain common child := by
 unfold WithdrawalDomain
 rw [association]
 exact NEC_SliceDomains.terminal_payment _ length

#print axioms transfer_caller
#print axioms withdrawal_caller
end NEC_PaymentDomains
