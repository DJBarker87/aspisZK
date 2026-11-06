import PCC_Scalar
set_option autoImplicit false
namespace PCC
open PCA
/-- Frozen POOL:301: owner short-circuit precedes panicking data_len;
try_borrow_data is entered only for the exact page length. -/
def zeroedReference (args : Nat × Key) : Reference Bool := fun s =>
  let account := s.loans.state.accounts args.1
  if account.owner != args.2.toList then Reference.pure false s
  else Reference.bind (dataLength args.1) (fun n =>
    if n != 8256 then Reference.pure false
    else withShared args.1 (fun payload =>
      Reference.pure (payload.bytes.all (· == 0)))) s

def RowSpec_POOL_301 (native : (Nat × Key) → Reference Bool) : Prop :=
  Reference.RowSpec (fun args s => args.1 < s.accountCount) native zeroedReference
end PCC
