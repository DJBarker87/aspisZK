import PCC_Reference
set_option autoImplicit false
namespace PCC
open PCA
structure PageArgs where
  guard : NLF_RefCell.Guard
  pool : Key
  page : UInt64
  first : UInt64
  roots : List Digest

def wordByte (value index : Nat) : UInt8 := UInt8.ofNat (value / 2^(8*index))
def digestByte (digest : Digest) (i : Nat) : UInt8 :=
  wordByte (digest[i/4]?.getD 0).toNat (i%4)
/-- Closed-form value of the frozen fill/header/ordered-root writes. The
source extent obligations are separate; no concrete 8256-byte reduction. -/
def pageByte (args : PageArgs) (i : Nat) : UInt8 :=
  if i < 4 then ([65,83,80,82] : Bytes)[i]?.getD 0
  else if i = 4 then 1
  else if i = 5 then 8
  else if i = 6 then 1
  else if i = 7 then 0
  else if i < 40 then args.pool[i-8]?.getD 0
  else if i < 48 then wordByte args.page.toNat (i-40)
  else if i < 56 then wordByte args.first.toNat (i-48)
  else if i < 58 then wordByte args.roots.length (i-56)
  else if i < 64 then 0
  else
    let slot := (i-64)/32
    match args.roots[slot]? with
    | none => 0
    | some root => digestByte root ((i-64)%32)

def pageImage (args : PageArgs) : Bytes := (List.range 8256).map (pageByte args)
end PCC
