import PCC_Shared
set_option autoImplicit false
namespace PCC
open PCA
/-- AccountInfo::data_len uses a panicking shared borrow, not try_borrow_data's
returned error. Its acquire/deref/drop prefix is preserved. -/
def dataLength (account : Nat) : Reference Nat := fun s =>
  let r := withShared account (fun payload => Reference.pure payload.bytes.length) s
  match r.reply with
  | .error _ => {r with reply := .abort "AccountInfo::data_len borrow panic"}
  | _ => r

def dataEmpty (account : Nat) : Reference Bool :=
  Reference.bind (dataLength account) (fun n => Reference.pure (n == 0))
end PCC
