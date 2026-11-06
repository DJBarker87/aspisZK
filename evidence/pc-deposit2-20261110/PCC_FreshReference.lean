import PCC_Scalar
import PCA_ProgramIds
set_option autoImplicit false
namespace PCC
open PCA
structure FreshArgs where
  account : Nat
  program : Key
  expected : Key
  bytes : Nat
/-- Frozen POOL:362, complete branches and short-lived shared scope. -/
def freshReference (args : FreshArgs) : Reference Preparation := fun s =>
  let a := s.loans.state.accounts args.account
  if a.key != args.expected.toList || a.executable || a.signer || !a.writable then
    Reference.error (.program 0x41532035) s
  else if a.owner == args.program.toList then
    withShared args.account (fun payload =>
      if payload.bytes.length != args.bytes || payload.bytes.any (· != 0) then
        Reference.error (.program 0x41532035)
      else Reference.pure Preparation.existingZeroed) s
  else if a.owner == system_program then
    Reference.bind (dataEmpty args.account) (fun empty =>
      if empty then Reference.pure Preparation.createOrAllocate
      else Reference.error (.program 0x41532035)) s
  else Reference.error (.program 0x41532035) s

def RowSpec_POOL_362 (native : FreshArgs → Reference Preparation) : Prop :=
  Reference.RowSpec (fun args s => args.account < s.accountCount) native freshReference
end PCC
